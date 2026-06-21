package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap => MLinkedHashMap}
import scala.jdk.CollectionConverters._
import scala.collection.mutable.Stack

import java.lang.{Class => JClass}

class NewDeleteTransformException(msg : String) extends Exception(msg)

object CCAstNewDeleteTransformer {

  val primitiveTypeClasses: Set[JClass[_ <: Type_specifier]] = Set(
    classOf[Tint], classOf[Tfloat], classOf[Tdouble],
    classOf[Tsigned], classOf[Tunsigned], classOf[Tshort],
    classOf[Tlong], classOf[Tchar], classOf[Tbool]
  )

  def isPrimitive(ts : Type_specifier): Boolean =
    primitiveTypeClasses.contains(ts.getClass)

  def isClassType(ts : Type_specifier): Boolean = ts match {
    case s: Tstruct => s.struct_or_union_spec_ match {
      case t: TagType => t.struct_or_union_.isInstanceOf[Class]
      case t: Tag     => t.struct_or_union_.isInstanceOf[Class]
      case _          => false
    }
    case _ => false
  }

  def classNameOf(ts: Type_specifier): String = ts match {
    case s: Tstruct => s.struct_or_union_spec_ match {
      case t: TagType => t.cident_
      case t: Tag     => t.cident_
      case _ =>
        throw new NewDeleteTransformException("Cannot extract class name from unnamed struct spec")
    }
    case _ =>
      throw new NewDeleteTransformException("Cannot extract class name from non-struct type")
  }

  def typeKey(ts: Type_specifier): String = ts match {
    case _: Tint      => "int"
    case _: Tfloat    => "float"
    case _: Tdouble   => "double"
    case _: Tsigned   => "signed"
    case _: Tunsigned => "unsigned"
    case _: Tshort    => "short"
    case _: Tlong     => "long"
    case _: Tchar     => "char"
    case _: Tbool     => "bool"
    case _ if isClassType(ts) => classNameOf(ts)
    case _ =>
      throw new NewDeleteTransformException(
        s"Unsupported type in new/delete expression: ${ts.getClass.getSimpleName}")
  }

  def newFuncName(ts: Type_specifier): String    = "__new_"    + typeKey(ts).replace("::", "_")

  def deleteFuncName(ts: Type_specifier): String = "__delete_" + typeKey(ts).replace("::", "_")

  case class NewTypeInfo(
    typeSpec           : Type_specifier,
    representativeArgs : Option[ListExp],
    origin             : SourceInfoProvider
  )


  def transform(program: Program): Program = {
    val printer = new PrettyPrinterNonStatic()

    // Type annotate such that we know which delete-function to invoke
    // when subexpression is Evar
    val annotated = CCAstTypeAnnotator(program)

    // Store each type called with new to know which helpers to add
    val exprCollector = new NewExprCollector
    annotated.accept(exprCollector, ())
    val collected = exprCollector.collectedTypes


    // Collect constructor parameters to be passed to helpers
    val ctorCollector = new CtorParamCollector
    program.accept(ctorCollector, ())

    // Prepends helper functions, rewrites calls to new and delete via either the helpers
    // or malloc/calloc and free.
    val transformer = new NewDeleteTransformer(collected, ctorCollector.ctorParams)
    val result = annotated.accept(transformer, ())

    result
  }
}

class NewExprCollector extends ComposVisitor[Unit] {
  import CCAstNewDeleteTransformer._

  val collectedTypes = new MLinkedHashMap[String, NewTypeInfo]

  override def visit(e : ENew, arg: Unit): ENew = isClassType(e.type_specifier_) match {
    case true =>
      val ts  = e.type_specifier_
      val key = typeKey(ts)
      val cls = isClassType(ts)

      val repArgs: Option[ListExp] = e.new_initializer_ match {
        case ni: NewInitArgs => Some(ni.listexp_)
        case _               => None
      }

      if (!collectedTypes.contains(key)) {
        collectedTypes(key) = NewTypeInfo(ts, repArgs, e)
      } else if (repArgs.isDefined && collectedTypes(key).representativeArgs.isEmpty) {
        // Upgrade existing entry: we now have concrete args to model the signature on
        collectedTypes(key) = collectedTypes(key).copy(representativeArgs = repArgs)
      }
      e.new_initializer_.accept(this, ())
      e
    case _ =>
      e.new_initializer_.accept(this, ())
      e
  }
}


/**
  Collect parameter declarations for each class, which is then used
  when creating helper functions. Needs to index classes with fully qualified
  names.
*/
class CtorParamCollector extends ComposVisitor[Unit] {
  val ctorParams = new MHashMap[String, ListParameter_declaration]

  private val classStack = new Stack[String]

  private def qualified(name: String): String =
    (classStack.reverse :+ name).mkString("::")

  override def visit(tag: Tag, arg: Unit): Tag = {
    tag.struct_or_union_ match {
      case _: Class =>
        // Push class scope, visit body, pop scope
        classStack.push(qualified(tag.cident_))
        tag.liststruct_dec_.asScala.foreach(_.accept(this, ()))
        classStack.pop()
      case _ =>
        // Descend into nested non-class structs/unions in case a class is inside
        tag.liststruct_dec_.asScala.foreach(_.accept(this, ()))
    }
    tag
  }

  override def visit(smf: SpecialMemberFunc, arg: Unit): SpecialMemberFunc = {
    smf.is_dtor_ match {
      case _: NotDtor if classStack.nonEmpty =>
        smf.direct_declarator_ match {
          case fd: NewFuncDec =>
            fd.parameter_type_ match {
              case allSpec: AllSpec =>
                // Only record the first constructor found (no overloading)
                if (!ctorParams.contains(classStack.top))
                  ctorParams(classStack.top) = allSpec.listparameter_declaration_
              case _ =>
            }
          case fd: OldFuncDec =>
            if (!ctorParams.contains(classStack.top))
              ctorParams(classStack.top) = new ListParameter_declaration
          case _ =>
        }
      case _ => // Destructor or outside a class, do nothing
    }
    smf
  }
}


/**
 Transforms program such that:
  1. `__new_C` / `__delete_C` helper functions are added globally for each
     class type C collected via the NewExprCollector
  2. Replaces all occurrences of `ENew` with calls to `__new_C`
  3. Replaces all occurrences of `EDelete` with call to either `free` (primitives) or
    `__delete_T()` (class types`
 */
class NewDeleteTransformer(
  collected  : MLinkedHashMap[String, CCAstNewDeleteTransformer.NewTypeInfo],
  ctorParams : MHashMap[String, ListParameter_declaration]
) extends ComposVisitor[Unit] with CopyAstLocation {

  import CCAstNewDeleteTransformer._

  private val copyAst = new CCAstCopyVisitor
  private val getName = new CCAstGetNameVistor
  private val rename  = new CCAstRenameInDeclarationVistor

  private def singleDeclSpec(ts: Type_specifier): ListDeclaration_specifier = {
    val l = new ListDeclaration_specifier
    l.add(new Type(ts))
    l
  }

  private def sizeofType(ts: Type_specifier): Exp = {
    val sq = new ListSpec_qual
    sq.add(new TypeSpec(ts))
    new Ebytestype(new PlainType(sq))
  }

  private def mallocOf(ts: Type_specifier): Exp = {
    val args = new ListExp
    args.add(sizeofType(ts))
    new Efunkpar(new Evar("malloc"), args)
  }

  private def callocOf(ts: Type_specifier): Exp = {
    val args = new ListExp
    args.add(sizeofType(ts))
    new Efunkpar(new Evar("calloc"), args)
  }

  private def freeCall(expr: Exp): Exp = {
    val args = new ListExp
    args.add(expr)
    new Efunkpar(new Evar("free"), args)
  }

  /**
    Deep-copy a parameter_declaration list.
    The copies are needed because the same ctor param list might be reused
    in multiple contexts (function signature + forwarded arg list).
   */
  private def copyParamList(src: ListParameter_declaration): ListParameter_declaration = {
    val dst = new ListParameter_declaration
    def renameArg(s: String) : String = "__new_arg_" + s
    src.asScala.foreach(p => dst.add(p.accept(copyAst, ()).accept(rename, renameArg(_))))

    dst
  }

  /**
    Build an argument list that forwards all named parameters in `params`.
    `More` / `OnlyType` / `Abstract` entries (which have no name) are skipped.
   */
  private def forwardedArgs(params: ListParameter_declaration): ListExp = {
    val args = new ListExp
    params.asScala.foreach {
      case tap: TypeAndParam      => args.add(new Evar(tap.declarator_.accept(getName, ())))
      case thp: TypeHintAndParam  => args.add(new Evar(thp.declarator_.accept(getName, ())))
      case _                      => // skip unnameable params
    }
    args
  }

  /**
   Generates function definition for `__new_T_`.

   For a class type `C`:
     class C* __new_C(<forwarded ctor params>) {
        class *C __tmp = malloc(sizeof(struct C));
        *__tmp = class C(<forwarded_params>); // Ctor call
        return __tmp;
     }

   */
  private def generateNewFunc(info: NewTypeInfo): Afunc = {
    val ts    = info.typeSpec
    val fname = newFuncName(ts)
    val setMissingLocation = new CCAstSetMissingLocationVisitor(info.origin) // New func gets same location as original call site

    val params: ListParameter_declaration = {
      // Use the constructor's parameter list from the class definition.
      val cname = classNameOf(ts)
      ctorParams.get(cname).map(copyParamList)
        .getOrElse(new ListParameter_declaration)
    }


    // T* __tmp = calloc(sizeof(T));
    val tmpDecSpec  = new ListDeclaration_specifier
    tmpDecSpec.add(new Type(ts))
    val tmpInitDecs = new ListInit_declarator
    tmpInitDecs.add(new InitDecl(
      new BeginPointer(new Point, new Name("__tmp")),
      new InitExpr(callocOf(ts))
    ))
    val stm1 = new DecS(new Declarators(tmpDecSpec, tmpInitDecs, new ListExtra_specifier))

    val lhs = new Epreop(new Indirection, new Evar("__tmp"))
    val rhs = {
      val cname = classNameOf(ts)
      new ECtor(new Class, cname, forwardedArgs(params))
    }
    val stm2 = new ExprS(new SexprTwo(new Eassign(lhs, new Assign, rhs)))

    val stm3 = new JumpS(new SjumpFive(new Evar("__tmp")))

    val body = new ListStm
    body.add(stm1)
    body.add(stm2)
    body.add(stm3)

    val retSpec = new ListDeclaration_specifier
    retSpec.add(new Type(ts))

    val f = new Afunc(new NewFunc(
      retSpec,
      new BeginPointer(new Point, new NewFuncDec(new Name(fname), new AllSpec(params))),
      new ScompTwo(body)
    ))

    f.accept(setMissingLocation, ())
    f
  }

  /**
    Generates __delete_T function, which deallocates a class object,
    where T::dtor is be called on the pointer before being freed.
  */
  private def generateDeleteFunc(info: NewTypeInfo): Afunc = {
    val ts    = info.typeSpec
    val fname = deleteFuncName(ts)

    val ptrParamSpec = singleDeclSpec(ts)
    val paramList    = new ListParameter_declaration
    paramList.add(new TypeAndParam(ptrParamSpec, new BeginPointer(new Point, new Name("__ptr"))))

    val body = new ListStm
    val dtorPar = new ListExp
    dtorPar.add(new Evar("__ptr"))
    body.add(new ExprS(new SexprTwo(new Efunkpar(new Evar(classNameOf(ts) ++ "::dtor"), dtorPar))))
    body.add(new ExprS(new SexprTwo(freeCall(new Evar("__ptr")))))

    val retSpec = new ListDeclaration_specifier
    retSpec.add(new Type(new Tvoid))

    new Afunc(new NewFunc(
      retSpec,
      new NoPointer(new NewFuncDec(new Name(fname), new AllSpec(paramList))),
      new ScompTwo(body)
    ))
  }


  override def visit(p: Progr, arg: Unit): Program = {
    val extDecls = new ListExternal_declaration

    // Emit generated helpers
    for ((_, info) <- collected) {

      // We only add a `__new_T` helper if info is a class, or if it the call had form
      // `__new_T(arg)`.
      if (isClassType(info.typeSpec))
        extDecls.add(generateNewFunc(info))

      // Add __delete_T for class types.
      // Primitive deletes are done via free().
      extDecls.add(generateDeleteFunc(info))
    }

    p.listexternal_declaration_.asScala.foreach { x =>
      val result = x.accept(this, arg)
      if (result != null) extDecls.add(result)
    }

    copyLocationInformation(p, new Progr(extDecls))
  }


  private def pointerDepthOf(newInit: InitPointer, acc: Int): Int = newInit.new_initializer_ match {
    case p : InitPointer => pointerDepthOf(p, acc + 1)
    case _ => acc
  }

  /**
    Rewrites `new T` calls as follows:

    Class types:
      `new C`       => `__new_C()`
      `new C()`     => `__new_C()`
      `new C(args)` => `__new_C(args)`
   */
  override def visit(eNew: ENew, arg: Unit): Exp = {
    val ts   = eNew.type_specifier_
    val init = eNew.new_initializer_
    val pDepth = init match {
      case p : InitPointer => pointerDepthOf(p, 1)
      case _ => 0
    }

    val result: Exp = {
      if (isPrimitive(ts)) {
        new ENew(ts, eNew.new_initializer_.accept(this, ()))
      }
      else if (isClassType(ts) && pDepth == 0) {
        val callArgs = new ListExp
        init match {
          case ni: NewInitArgs =>
            ni.listexp_.asScala.foreach(e => callArgs.add(e.accept(this, ())))
          case _ => // Do nothing
        }
        new Efunkpar(new Evar(newFuncName(ts)), callArgs)
      } else {
        throw new NewDeleteTransformException(
          s"Unsupported type in new expression at line ${eNew.line_num}, col ${eNew.col_num}")
      }
    }

    copyLocationInformation(eNew, result)
  }

  /**
    Rewrites `delete expr` as follows:
      Primitives  => `free(expr)`
      Class C obj => `__delete_C(expr)`
      Otherwise   => `free(expr)` (fallback)
   */
  override def visit(eDelete: EDelete, arg: Unit): Exp = {
    val transformedExpr = eDelete.exp_.accept(this, ())
    copyLocationInformation(
      eDelete,
      buildDeleteCall(transformedExpr, eDelete.exp_))
  }

  /**
    Rewrites `delete (expr)` via same rules as above.
   */
  override def visit(eDeleteParen: EDeleteParen, arg: Unit): Exp = {
    val transformedExpr = eDeleteParen.exp_.accept(this, ())
    copyLocationInformation(
      eDeleteParen,
      buildDeleteCall(transformedExpr, eDeleteParen.exp_))
  }

  /**
    Dispatches correct delete-replacement via the type of the expression.
    This requires the expression used with delete to be an `Evar`, due to
    it relying on the program being type annotated.
   */
  private def buildDeleteCall(transformedExpr: Exp, originalExpr: Exp): Exp = {
    resolveType(originalExpr) match {
      case Some(ts) if isPrimitive(ts) =>
        freeCall(transformedExpr)

      case Some(ts) if isClassType(ts) =>
        val args = new ListExp
        args.add(transformedExpr)
        new Efunkpar(new Evar(deleteFuncName(ts)), args)

      case _ =>
        freeCall(transformedExpr)
    }
  }

  /**
    Helper to resolve type of an expression.
    Works reliably for `EvarWithType` and a dereference of an `EvarWithType`.

    If called on an expression that doesn't resolve to one of the above,
    this will cause `buildDeleteCall` to simply call `free`.
   */
  private def resolveType(expr: Exp): Option[Type_specifier] = expr match {
    case ev: EvarWithType =>
      // listdeclaration_specifier_ carries the declared type of the variable
      ev.listdeclaration_specifier_.asScala.collectFirst {
        case t: Type => t.type_specifier_
      }

    case ep: Epreop =>
      ep.unary_operator_ match {
        case _: Indirection => resolveType(ep.exp_)
        case _              => None
      }

    case _ =>
      None
  }
}
