package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._
import tricera.concurrency.CCAstUtils.isStackPtr

import scala.collection.mutable.{HashMap => MHashMap, MutableList}
import scala.util.{Try,Success,Failure}
import scala.collection.JavaConverters._
import scala.collection.mutable.Buffer


class CallSiteTransformationException(msg : String) extends Exception(msg)

/*
  Vistor to extract the "Declarator" part from an Init_declaration
*/
class CCAstGetDeclaratorVistor extends AbstractVisitor[Declarator, Unit] {
  private val copyAst = new CCAstCopyVisitor

  /* Init_declarator */
  override def visit(dec: OnlyDecl, arg: Unit): Declarator = { dec.declarator_.accept(copyAst, arg); }
  override def visit(dec: InitDecl, arg: Unit): Declarator = { dec.declarator_.accept(copyAst, arg); }
  override def visit(dec: HintDecl, arg: Unit): Declarator = { dec.declarator_.accept(copyAst, arg); }
  override def visit(dec: HintInitDecl, arg: Unit): Declarator = { dec.declarator_.accept(copyAst, arg); }
}

/*
  Vistor class to remove one level of indirection ("dereference a pointer").
*/
class CCAstRemovePointerLevelVistor extends ComposVisitor[Unit] {
  /* Declarator */
  override def visit(dec: BeginPointer, arg: Unit) = { new NoPointer(dec.direct_declarator_.accept(this, arg)); }
}

/*
  Vistor class to rename a declaration or definition.
*/
class CCAstRenameInDeclarationVistor extends ComposVisitor[String => String] {
  /* Direct_declarator */
  override def visit(dec: Name, rename: String => String): Name = { new Name(rename(dec.cident_)) }
}

/*
  Vistor class to transform any declaration to a scalar variable declaration,
  removing e.g. array or function declaration elements.
*/
class CCAstDeclaratorToNameVistor extends ComposVisitor[String => String] {
  /* Direct_declarator */
  override def visit(dec: Name, rename: String => String): Name = { new Name(rename(dec.cident_)) }
  override def visit(dec: ParenDecl, rename: String => String): Name = { dec.declarator_ match {
      case ptr: BeginPointer => ptr.direct_declarator_.accept(this, rename).asInstanceOf[Name]
      case d: NoPointer => d.direct_declarator_.accept(this, rename).asInstanceOf[Name]
    } 
  }
  override def visit(dec: InitArray, rename: String => String): Name = { dec.direct_declarator_.accept(this, rename).asInstanceOf[Name] }
  override def visit(dec: Incomplete, rename: String => String): Name = { dec.direct_declarator_.accept(this, rename).asInstanceOf[Name] }
  override def visit(dec: MathArray, rename: String => String): Name = { dec.direct_declarator_.accept(this, rename).asInstanceOf[Name] }
  override def visit(dec: NewFuncDec, rename: String => String): Name = { dec.direct_declarator_.accept(this, rename).asInstanceOf[Name] }
  override def visit(dec: OldFuncDec, rename: String => String): Name = { dec.direct_declarator_.accept(this, rename).asInstanceOf[Name] }
}

/*
  Vistor to extract a function body from a function definition.
*/
class CCAstGetFunctionBodyVistor extends AbstractVisitor[Compound_stm, Unit] {
  val copyAst = new CCAstCopyVisitor
  /* Function_def */
  override def visit(defn: AnnotatedFunc, arg: Unit) = { 
    defn.compound_stm_.accept(copyAst, arg)
  }
  override def visit(defn: NewFuncInt, arg: Unit) = {
    defn.compound_stm_.accept(copyAst, arg)
  }
  override def visit(defn: NewFunc, arg: Unit) = { 
    defn.compound_stm_.accept(copyAst, arg)
  }
}

/*
  Vistor to extract the "Parameter_type" part from a Declarator
*/
class CCAstGetParametersVistor extends AbstractVisitor[ListParameter_declaration, Unit] {
    /* Declarator */
    override def visit(dec: BeginPointer, arg: Unit) = { dec.direct_declarator_.accept(this, ()) }
    override def visit(dec: NoPointer, arg: Unit) = { dec.direct_declarator_.accept(this, ()) }

    /* Direct_declarator */
    override def visit(dec: NewFuncDec, arg: Unit) = { dec.parameter_type_.accept(this, ()) }
    override def visit(dec: OldFuncDec, arg: Unit) = { new ListParameter_declaration }

    /* Parameter_type */
    override def visit(spec: AllSpec, arg: Unit) = { spec.listparameter_declaration_ }
}

/*
  Vistor to convert function parameters to CCAstDeclaration.
*/
class CCAstParamToAstDeclarationVistor extends AbstractVisitor[CCAstDeclaration, Unit] {
  private val copyAst = new CCAstCopyVisitor

  /* Init_declarator */
  override def visit(param: TypeAndParam, arg: Unit) = {
    toDeclarationData(param.listdeclaration_specifier_, param.declarator_)
  }

  override def visit(param: TypeHintAndParam, arg: Unit) = { 
    toDeclarationData(param.listdeclaration_specifier_, param.declarator_)
  }

  private def toDeclarationData(decSpecs: ListDeclaration_specifier, declarator: Declarator) = {
    new CCAstDeclaration(
      copyAst(decSpecs),
      new OnlyDecl(declarator.accept(copyAst, ())),
      new ListExtra_specifier)
  }
}

/*
  Vistor to get declared type from a specifier.
*/
class CCAstGetTypeVisitor extends AbstractVisitor[Boolean, MutableList[Type_specifier]] {
  /* Declaration_specifier */
  override def visit(spec: Type, types: MutableList[Type_specifier]) = { types += spec.type_specifier_; true }
  override def visit(spec: Storage, types: MutableList[Type_specifier]) = { false }
  override def visit(spec: SpecProp, types: MutableList[Type_specifier]) = { false }
  override def visit(spec: SpecFunc, types: MutableList[Type_specifier]) = { false }
}

private object CCAstUtils {
  def isStackPtrInitialized(identifier: EvarWithType): Boolean = {
    // TODO: Check that init value is address-of operator
    identifier.init_declarator_ match {
      case _: HintInitDecl => true
      case _: InitDecl => true
      case _ => false
    }
  }

  def isStackPtr(exp: Exp): Boolean = {
    exp match {
      case x: Epreop =>
          x.unary_operator_ match {
              case _: Address => true
              case _ => false
          }
      case x: EvarWithType if (isStackPtrInitialized(x)) => true
      case _ => false
    }
  }
}

/*
    Vistor to replace given pointers with global variables.
*/
class CCAstPointerToGlobalVisitor extends ComposVisitor[Map[String, CCAstDeclaration]] {
  private val getName = new CCAstGetNameVistor
  /* Stm */
  override def visit(stm: CompS, replacements: Map[String, CCAstDeclaration]): Stm = {
    val compound_stm_ = stm.compound_stm_.accept(this, replacements);
    new CompS(compound_stm_);
  }

  /* Exp */
  override def visit(exp: Epreop, replacements: Map[String, CCAstDeclaration]): Exp = {
    exp.unary_operator_ match {
      case op: Indirection => exp.exp_ match {
        // *id ...
        case id: EvarWithType => replacements.get(id.cident_) match {
          case Some(global) => global.toEvarWithType();
          case None => super.visit(exp, replacements)
        }
        // *exp
        case _ => super.visit(exp, replacements)
      }
      case _ => super.visit(exp, replacements)
    }
  }

  override def visit(exp: Epoint, replacements: Map[String, CCAstDeclaration]): Exp = {
    exp.exp_ match {
      // id->...
      case id: EvarWithType => replacements.get(id.cident_) match {
        case Some(global) => new Eselect(global.toEvarWithType(), exp.cident_);
        case None => super.visit(exp, replacements)
      }
      // exp->...
      case _ => super.visit(exp, replacements)
    }
  }

  override def visit(exp: EvarWithType, replacements: Map[String, CCAstDeclaration]): Exp = {
    replacements.get(exp.cident_) match {
      case Some(global) => new Epreop(new Address(), global.toEvarWithType())
      case None => super.visit(exp, replacements)
    }
  }

  // override def visit(callSite: Efunkpar, replacements: Map[String, CCAstDeclaration]): Exp = {
  //   callSite.listexp_.asScala.find(CCAstUtils.isStackPtr) match {
  //     case None =>
  //       super.visit(callSite, transforms)
  //     case Some(_) => 
  //       super.visit(callSite, transforms)
  //       // TODO: This will not work if function is invoked through
  //       //   a pointer. Then we don't know the name of the function
  //       //   being invoked. Therefore we can't create/invoke a
  //       //   transformed function.
  //       val tform = CallSiteTransform(functionDefinitions(callSite.accept(getName, ())), callSite.listexp_)
  //       transforms += tform
  //       tform.wrappedInvocation()
  //   }
  // }
}

/*
  CallSiteTransform represents all the transforms that needs to be
  done of a specific function and at a specific call site in order
  to replace arguments pointing towards the stack (stack pointer
  arguments), with global variables.
*/
object CallSiteTransform {
  private val copyAst = new CCAstCopyVisitor
  private val getDeclarator = new CCAstGetDeclaratorVistor
  private val getFunctionDeclaration = new CCAstGetFunctionDeclarationVistor
  private val getParameters = new CCAstGetParametersVistor
  private val getName = new CCAstGetNameVistor
  private val toName = new CCAstDeclaratorToNameVistor
  private val rename = new CCAstRenameInDeclarationVistor
  private val getFunctionBody = new CCAstGetFunctionBodyVistor
  private val removePointer = new CCAstRemovePointerLevelVistor
  private val toCCAstDeclaration = new CCAstParamToAstDeclarationVistor

  def apply(funcDef: Function_def, args: ListExp): CallSiteTransform = {
    new CallSiteTransform(funcDef, copyAst(args))
  }

  private def wrapIdentifier(id: String) = {
    // We use the non-printable 0x1F US (Unit Separator)
    // as a means to get a new identifier name not colliding
    // with something existing in the original source.
    f"wrapped\u001F${id}"
  }

  private def onlyWrapIdentifier(matchId: String)(id: String) = {
    id match {
      case `matchId` => wrapIdentifier(id)
      case _ => id
    }
  }

  private def transformIdentifier(id: String): String = { 
    f"global\u001F${id}" 
  }

  private def onlyTransformIdentifier(matchId: String)(id: String): String = {
    id match {
      case `matchId` => transformIdentifier(id)
      case _ => id
    }
  }

  private def resultIdentifier(id: String): String = { 
    f"result\u001F${id}" 
  }
}

class CallSiteTransform(funcDef: Function_def, args: ListExp) {
  import CallSiteTransform._

  private val (specifiers, declarator) = {
    val (spec, dec) = funcDef.accept(getFunctionDeclaration, ())
    (spec, dec.accept(getDeclarator, ()))
  }
  val originalName = declarator.accept(getName, ())
  private val params = declarator.accept(getParameters, ())
  private val keptArgs = {
    val kept = new ListExp
    args.asScala
    .withFilter(!isStackPtr(_))
    .foreach(param => kept.add(param.accept(copyAst, ())))
    kept
  }
  private val keptParams = { 
    val kept = new ListParameter_declaration
    params.asScala.zip(args.asScala)
    .withFilter({case (param, arg) => !isStackPtr(arg)})
    .map({case (param, arg) => param.accept(copyAst, ())})
    .foreach(param => kept.add(param))
    kept
  }
  private val removedParams = {
    val removed = new ListParameter_declaration
    params.asScala.zip(args.asScala)
    .withFilter({case (param, arg) => isStackPtr(arg)})
    .map({case (param, arg) => param.accept(copyAst, ())})
    .foreach(param => removed.add(param))
    removed
  }

  def wrapperDefinition(): External_declaration = {
    new Afunc(
      new NewFunc(
        copyAst(specifiers),
        declarator.accept(rename, onlyWrapIdentifier(originalName)(_)),
        createWrapperBody()))
  }

  def wrapperDeclaration(): CCAstDeclaration = {
    val funcDec = if (params.size > 0) {
      new NewFuncDec(new Name(wrapIdentifier(originalName)), new AllSpec(copyAst(params)))
    } else {
      new OldFuncDec(new Name(wrapIdentifier(originalName)))
    }
    new CCAstDeclaration(
      copyAst(specifiers),
      new OnlyDecl(new NoPointer(funcDec)),
      new ListExtra_specifier)
  }

  def wrapperInvocation(): Efunkpar = {
    new Efunkpar(
      new EvarWithType(
        wrapIdentifier(originalName),
        copyAst(specifiers),
        new OnlyDecl(declarator.accept(rename, onlyWrapIdentifier(originalName)(_)))),
      copyAst(args))
  }

  def transformedDefinition(): External_declaration = {
    val funcDec = transformedDeclaration().toEvarWithType()
    new Afunc(
      new NewFunc(
        funcDec.listdeclaration_specifier_,
        funcDec.init_declarator_.accept(getDeclarator, ()),
        createTransformedBody(funcDef.accept(getFunctionBody, ()))))
  }

  def globalVariableDeclarations(): ListExternal_declaration = {
    val globals = new ListExternal_declaration
    for (param <- removedParams.asScala) {
      globals.add(toGlobalDeclaration(param).toGlobal())
    }
    globals
  }

  def transformedDeclaration() = {
    val funcDec = if (keptParams.size > 0) {
      new NewFuncDec(new Name(transformIdentifier(originalName)), new AllSpec(copyAst(keptParams)))
    } else {
      new OldFuncDec(new Name(transformIdentifier(originalName)))
    }
    new CCAstDeclaration(
      copyAst(specifiers),
      new OnlyDecl(new NoPointer(funcDec)),
      new ListExtra_specifier)
  }

  private def toGlobalDeclaration(param: Parameter_declaration) = {
    param
      .accept(rename, toGlobalVariableName(_))
      .accept(removePointer, ())
      .accept(toCCAstDeclaration, ())
  }

  private def toGlobalVariableName(name: String) = {
    f"global\u001F${originalName}\u001F${name}"
  }

  private def createWrapperBody(): Compound_stm = {
    def paramToGlobalAssignment(param: CCAstDeclaration, global: CCAstDeclaration) = {
      new ExprS(new SexprTwo(new Eassign(
        global.toEvarWithType(),
        new Assign, 
        new Epreop(new Indirection(), param.toEvarWithType()))))
    }

    def globalToParamAssignment(param: CCAstDeclaration, global: CCAstDeclaration) = {
      new ExprS(new SexprTwo(
          new Eassign(
            new Epreop(new Indirection(), param.toEvarWithType()),
            new Assign,
            global.toEvarWithType())))
    }

    def getResultDeclaration(): Option[CCAstDeclaration] = {
      val getType = new CCAstGetTypeVisitor
      val types = new MutableList[Type_specifier]
      specifiers.asScala.foreach(s => s.accept(getType, types))
      types.contains(new Tvoid) match {
        case true => 
          None
        case false =>
          Some(CCAstDeclaration(copyAst(specifiers), new OnlyDecl(declarator.accept(toName, resultIdentifier(_)))))
      }
    }

    def callTransformedFunctionExp() = {
      val func = transformedDeclaration()
      val callExp = if (keptParams.size > 0) {
        new Efunkpar(func.toEvarWithType(), copyAst(keptArgs))
      } else {
        new Efunk(func.toEvarWithType())
      }

      val statement = getResultDeclaration() match {
        case None => new ExprS(new SexprTwo(callExp))
        case Some(resultVar) =>
          new ExprS(new SexprTwo(new Eassign(resultVar.toEvarWithType(), new Assign, callExp)))
      }
      statement
    }

    def returnFromWrapper() = {
      getResultDeclaration() match {
        case None => new JumpS(new SjumpFour())
        case Some(resultVar) => new JumpS(new SjumpFive(resultVar.toEvarWithType()))
      }
    }

    val pairs = removedParams.asScala.map(p => (p.accept(toCCAstDeclaration,()), toGlobalDeclaration(p)))
    val body = new ListStm

    getResultDeclaration() match {
      case None => ;
      case Some(decl) => body.add(new DecS(decl.toDeclarators()))
    }

    for ((param, global) <- pairs) {
      body.add(paramToGlobalAssignment(param, global))
    }
 
    body.add(callTransformedFunctionExp())

    for ((param, global) <- pairs.reverse) {
      body.add(globalToParamAssignment(param, global))
    }

    body.add(returnFromWrapper())

    new ScompTwo(body)
  }

  private def createTransformedBody(body: Compound_stm) = {
    // Take the original body, replace "removedParams" in the body
    // with the corresponding global variables.
    val paramToGlobalVar = removedParams.asScala.map(p => (p.accept(getName,()), toGlobalDeclaration(p))).toMap
    body.accept(new CCAstPointerToGlobalVisitor, paramToGlobalVar)
  }
}

class CallSiteTransforms extends MutableList[CallSiteTransform]

object  CCAstStackPtrArgToGlobalTransformer {
  def apply(program: Program) = {
    val transformer = new CCAstStackPtrArgToGlobalTransformer
    program.accept(transformer, new CallSiteTransforms)
  }
}

class CCAstStackPtrArgToGlobalTransformer extends ComposVisitor[CallSiteTransforms] {
  // Idea: For each function invocation that has arguments that points to
  //   memory allocated on the stack (stack pointers), introduce two new
  //   functions, and for each stack pointer argument a global variable.
  //   The first function, called the "wrapper", is substituted for at the
  //   call site. The wrapper takes the same arguments as the original
  //   function. However, the wrapper body just assigns the global variables
  //   with contents from the stack, and the calls the second function.
  //   The scecond function, called the "transformed" function, is a function
  //   with the same body as the original, but arguments that are stack
  //   pointers are replaced with the global variables.
  //   The wrapper function will eventually be inlined by TriCera. Hence,
  //   TriCera will check a version of the program where all stack pointers
  //   are replaced with global variables, and assignments to/from them.
  //
  // TODO: This will not work if the function is invoked through a
  //   pointer. Then we don't know the name of the function being
  //   invoked and cannot add the corresponding function with global
  //   variables.

  private val getName = new CCAstGetNameVistor
  private val copyAst = new CCAstCopyVisitor
  private val rename = new CCAstRenameInDeclarationVistor
  private val functionDefinitions = new MHashMap[String, Function_def]

  /* Program */
  override def visit(progr: Progr, callSiteTransforms: CallSiteTransforms): Program = {
    def distinctBy[A, K](f: A => K, seq: Iterable[A]) = {
      seq.groupBy(f).map({ case (key, buffer) => buffer.head })
    }

    def processExternalDeclarations(extDecl: ListExternal_declaration, transforms: CallSiteTransforms) = {
      val extDeclarations = new ListExternal_declaration
      for (x <- extDecl.asScala)
      {
        extDeclarations.add(x.accept(this, transforms));
      }

      transforms ++= processCallSiteTransforms(callSiteTransforms)

      extDeclarations
    }

    def processCallSiteTransforms(transforms: CallSiteTransforms): CallSiteTransforms = {
      def onlyRename(matchId: String, newId: String)(id: String) = {
        id match {
          case `matchId` => newId
          case _ => id
        }
      }
      // TODO: Watch out for recursion.
      val updatedTransforms = new CallSiteTransforms
      val nested = new CallSiteTransforms
      for (t <- transforms) {
        val wrapper = t.wrapperDefinition()
        functionDefinitions.put(wrapper.accept(getName, ()), wrapper.asInstanceOf[Afunc].function_def_)
        val transformed = t.transformedDefinition()
        val fullTransformed = transformed.accept(this, nested).accept(rename, onlyRename(transformed.accept(getName, ()), t.originalName)(_))
        updatedTransforms += new CallSiteTransform(fullTransformed.asInstanceOf[Afunc].function_def_, t.wrapperInvocation().listexp_)
      }
      if (nested.size > 0) {
        nested ++= processCallSiteTransforms(nested)
      }
      updatedTransforms ++= nested
    }

    def transformedFunctions(transforms: CallSiteTransforms): ListExternal_declaration = {
      val funcs = new ListExternal_declaration 
      distinctBy({ v:External_declaration => v.accept(getName, ())}, transforms.reverse.map(t => t.transformedDefinition())).foreach(v => funcs.add(v))
      funcs
    }

    def wrapperDeclarations(transforms: CallSiteTransforms): ListExternal_declaration = {
      val funcDecls = new ListExternal_declaration 
      val q = transforms.reverse.map(t => t.wrapperDeclaration().toGlobal())
      distinctBy({ v:External_declaration => v.accept(getName, ())}, q).foreach(v => funcDecls.add(v))
//      distinctBy({ v:External_declaration => v.accept(getName, ())}, transforms.reverse.map(t => t.wrapperDeclaration().toGlobal())).foreach(v => funcDecls.add(v))
      funcDecls
    }

    def getNewGlobalVariables(transforms: CallSiteTransforms): ListExternal_declaration = {
      val globs = new ListExternal_declaration
      val newGlobals = transforms.flatMap(t => t.globalVariableDeclarations().asScala)
      distinctBy({ v:External_declaration => v.accept(getName, ())}, newGlobals).foreach(v => globs.add(v))
      globs
    }

    def wrapperFunctions(transforms: CallSiteTransforms): ListExternal_declaration = {
      val funcs = new ListExternal_declaration
      val wrappers = transforms.map(t => t.wrapperDefinition())
      distinctBy({ v:External_declaration => v.accept(getName, ())}, wrappers).foreach(v => funcs.add(v))
      funcs
    }

    def isMainDefinition(dec: External_declaration): Boolean = dec match {
      case funcDef: Afunc if (funcDef.function_def_.accept(getName, ()) == "main") => true
      case _ => false
    }

    val declarations = processExternalDeclarations(progr.listexternal_declaration_, callSiteTransforms)
    val mainDefIndex = declarations.lastIndexOf(declarations.asScala.find(isMainDefinition(_)).get)

    declarations.addAll(mainDefIndex, wrapperFunctions(callSiteTransforms))
    declarations.addAll(mainDefIndex, transformedFunctions(callSiteTransforms))
    declarations.addAll(mainDefIndex, wrapperDeclarations(callSiteTransforms))
    declarations.addAll(mainDefIndex, getNewGlobalVariables(callSiteTransforms))

    return new Progr(declarations);
  }

  override def visit(func: Afunc, transforms: CallSiteTransforms): External_declaration = {
    functionDefinitions.put(
      func.function_def_.accept(getName, ()),
      func.function_def_.accept(copyAst, ()))
    super.visit(func, transforms)
  }

  override def visit(callSite: Efunkpar, transforms: CallSiteTransforms): Exp = {
    callSite.listexp_.asScala.find(CCAstUtils.isStackPtr) match {
      case None =>
        super.visit(callSite, transforms)
      case Some(_) => 
        super.visit(callSite, transforms)
        // TODO: This will not work if function is invoked through
        //   a pointer. Then we don't know the name of the function
        //   being invoked. Therefore we can't create/invoke a
        //   transformed function.
        val tform = CallSiteTransform(functionDefinitions(callSite.accept(getName, ())), callSite.listexp_)
        transforms += tform
        tform.wrapperInvocation()
    }
  }
}