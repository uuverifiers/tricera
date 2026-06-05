/**
 * Copyright (c) 2026 Linus Hellström. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package tricera.concurrency

import concurrent_c._
import concurrent_c.PrettyPrinterNonStatic
import concurrent_c.Absyn._

import scala.collection.mutable.{HashMap => MHashMap, ListBuffer}
import scala.jdk.CollectionConverters._
import scala.collection.mutable.Stack

class ClassTransformException(msg: String) extends Exception(msg)

object CCAstClassTransformer {

  case class ClassDefInfo(
    classDecs:  ListBuffer[Struct_dec],
    classFuncs: ListBuffer[Afunc]
  )

  private val printer = new PrettyPrinterNonStatic()

  def transform(program: Program): Program = {

    val collector = new ClassDefCollector
    program.accept(collector, (null, null))

    val collectionResult = collector.collectedClassDefs
    if (collectionResult.isEmpty) return program

    val transformed = program.accept(new ClassTransformer(collectionResult), (null, null))

    transformed
  }
}

// When we collect class metadata, we use this visitor to store them with their fully
// qualified name.
class RenameClassVisitor extends CCAstCopyWithLocation[MHashMap[String, String]] {

  override def visit(dec: Tag, classMap: MHashMap[String, String]): Struct_or_union_spec =
    dec.struct_or_union_ match {
      case _: Class =>
        val newName      = classMap.getOrElse(dec.cident_, dec.cident_)
        val listStructDec = new ListStruct_dec
        dec.liststruct_dec_.forEach(s => listStructDec.add(s.accept(this, classMap)))
        new Tag(dec.struct_or_union_, newName, listStructDec)
      case _ => dec
    }

  override def visit(dec: TagType, classMap: MHashMap[String, String]): Struct_or_union_spec =
    dec.struct_or_union_ match {
      case _: Class =>
        val newName = classMap.getOrElse(dec.cident_, dec.cident_)
        new TagType(dec.struct_or_union_, newName)
      case _ => dec
    }
}

class IsClassVisitor extends AbstractVisitor[Boolean, Unit] {

  def structDecContainsClass(s: Struct_dec): Boolean = innerStructDec(s) match {
    case st: Structen      => containsClassType(st.listspec_qual_)
    case nd: StructenNoDec => containsClassType(nd.listspec_qual_)
    case _                 => false
  }

  private def innerStructDec(sd: Struct_dec): Struct_dec = sd match {
    case as: AccSpec => innerStructDec(as.struct_dec_)
    case other       => other
  }

  private def containsClassType(specs: java.util.List[_]): Boolean =
    specs.asScala.exists {
      case ts: TypeSpec => ts.type_specifier_.accept(this, ())
      case _            => false
    }


  override def visit(s: Tstruct, arg: Unit): Boolean  = s.struct_or_union_spec_.accept(this, ())
  override def visitDefault(t: Type_specifier, arg: Unit): Boolean = false

  override def visit(s: Tag, arg: Unit): Boolean      = s.struct_or_union_.accept(this, ())
  override def visit(s: Unique, arg: Unit): Boolean   = s.struct_or_union_.accept(this, ())
  override def visit(s: TagType, arg: Unit): Boolean  = s.struct_or_union_.accept(this, ())
  override def visitDefault(s: Struct_or_union_spec, arg: Unit): Boolean = false

  override def visit(s: Class, arg: Unit): Boolean    = true
  override def visitDefault(s: Struct_or_union, arg: Unit): Boolean = false
}

class ClassDefCollector extends ComposVisitor[(ListBuffer[Struct_dec], ListBuffer[Afunc])] {
  import CCAstClassTransformer._

  val collectedClassDefs = new MHashMap[String, ClassDefInfo]

  private val getName      = new CCAstGetNameVistor
  private val rename       = new CCAstRenameInDeclarationVistor
  private val isClass      = new IsClassVisitor
  private val classStack   = new Stack[String]
  private val classMap     = new MHashMap[String, String]

  private def qualifiedName(name: String): String =
    (classStack.reverse :+ name).mkString("::")

  private def isFuncOrConsDec(dir: Direct_declarator): Boolean =
    dir.isInstanceOf[NewFuncDec] || dir.isInstanceOf[OldFuncDec] || dir.isInstanceOf[ClassCons]

  private def isValidStructField(decl: Decl): Boolean = decl.declarator_ match {
    case p:  BeginPointer => !isFuncOrConsDec(p.direct_declarator_)
    case np: NoPointer    => !isFuncOrConsDec(np.direct_declarator_)
    case _                => false // Should never happen
  }

  // Unwraps access specifiers
  private def innerStructDec(sd: Struct_dec): Struct_dec = sd match {
    case as: AccSpec => innerStructDec(as.struct_dec_)
    case other       => other
  }


  // Creates a new function declaration for a member function, with an added struct parameter
  private def makeNewFuncDec(dd: Direct_declarator, renameArg: String => String): Direct_declarator = dd match {
    case fd: NewFuncDec =>
      new NewFuncDec(fd.direct_declarator_.accept(rename, renameArg), fd.parameter_type_)
    case fd: OldFuncDec =>
      new OldFuncDec(fd.direct_declarator_.accept(rename, renameArg))
  }

  // Converts member function definitions (Struct_dec) into global ones (Afunc)
  private def methodAsAfunc(className: String, s: Structen, f: ClassFunc): Afunc = {
    val listDeclSpecs = new ListDeclaration_specifier
    s.listspec_qual_.asScala.collect { case qs: QualSpec => new SpecProp(qs.type_qualifier_) }
      .foreach(listDeclSpecs.add)
    s.listspec_qual_.asScala.collect { case ts: TypeSpec => new Type(ts.type_specifier_) }
      .foreach(listDeclSpecs.add)


    // We store member functions qualified with fully qualified name of enclosing class
    val renamedDec = f.declarator_ match {
      case bp: BeginPointer => new BeginPointer(bp.pointer_, makeNewFuncDec(bp.direct_declarator_, qualifiedName))
      case np: NoPointer    => new NoPointer(makeNewFuncDec(np.direct_declarator_, qualifiedName))
      case _ => f.declarator_
    }

    new Afunc(new NewFunc(listDeclSpecs, renamedDec, f.compound_stm_))
  }

  // Visits member function definitions (constructors and destructors) and stores them in the class map.
  override def visit(fun: SpecialMemberFunc, decls: (ListBuffer[Struct_dec], ListBuffer[Afunc])): SpecialMemberFunc = {
    val suffix = fun.is_dtor_ match {
      case _: Dtor => "::dtor"
      case _       => "::ctor" // TODO: Needs to be changed if we want to support other special member functions
    }
    val className = classMap(classStack.head)
    val qualifiedCurrent: Any => String = _ => classMap(classStack.head) ++ suffix
    val voidReturn = {
      val lds = new ListDeclaration_specifier
      lds.add(new Type(new Tvoid))
      lds
    }

    val processedFunc = new NoPointer(makeNewFuncDec(fun.direct_declarator_, qualifiedCurrent))
    decls._2 += new Afunc(new NewFunc(voidReturn, processedFunc, fun.compound_stm_))

    fun
  }

  private def collectClassMetadata(className: String, s: Structen, decls: (ListBuffer[Struct_dec], ListBuffer[Afunc])): Unit = {
    // If the Struct_dec is a class, we have already visited it, meaning it has been collected.
    if (isClass.structDecContainsClass(s)) return

    val fields = s.liststruct_declarator_.asScala.collect {
      case decl: Decl if isValidStructField(decl) => decl
    }
    val functions = s.liststruct_declarator_.asScala.collect {
      case f: ClassFunc => methodAsAfunc(className, s, f)
    }

    if (fields.nonEmpty) {
      val listStructDec = new ListStruct_declarator
      fields.foreach(listStructDec.add)
      decls._1 += new Structen(s.listspec_qual_, listStructDec, s.break_)
    }
    functions.foreach(decls._2 += _)
  }

  // Entry point for class collection
  override def visit(c: Tag, arg: (ListBuffer[Struct_dec], ListBuffer[Afunc])): Tag =
    c.struct_or_union_ match {
      case _: Class =>
        val className = c.cident_
        val qualName  = if (classStack.isEmpty) { classMap.clear(); className } else qualifiedName(className) // get fully qualified name if nested
        classStack.push(className)
        classMap.put(className, qualName)

        val decls = (new ListBuffer[Struct_dec], new ListBuffer[Afunc])
        c.liststruct_dec_.forEach(_.accept(this, decls))

        c.liststruct_dec_.asScala
          .map(innerStructDec)
          .collect { case s: Structen => s }
          .foreach(s => collectClassMetadata(qualName, s, decls))

        classStack.pop()
        collectedClassDefs.put(qualName, ClassDefInfo(decls._1, decls._2))
        c

      case _ => c
    }
}

class ClassTransformer(
  val collectedDefs: MHashMap[String, CCAstClassTransformer.ClassDefInfo]
) extends CCAstCopyWithLocation[Any] {

  private val getDeclarator          = new CCAstGetDeclaratorVistor
  private val getParameters          = new CCAstGetParametersVistor
  private val getFunctionDeclaration = new CCAstGetFunctionDeclarationVistor
  private val copyAst                = new CCAstCopyVisitor
  private val getFuncBody            = new CCAstGetFunctionBodyVistor
  private val getName                = new CCAstGetNameVistor
  private val getType                = new CCAstGetTypeVisitor
  private val isClass                = new IsClassVisitor


  private def globalStruct(className: String, structDecs: ListBuffer[Struct_dec]): External_declaration = {
    val specs         = new ListDeclaration_specifier
    val listStructDec = new ListStruct_dec
    structDecs.foreach(listStructDec.add)
    specs.add(new Type(new Tstruct(new Tag(new Struct, className, listStructDec))))
    new Global(new NoDeclarator(specs, new ListExtra_specifier))
  }

  private def factoryFuncName(className: String): String =
    "__create_" + className

  // Creates helper function `__create_C` which
  // declares a temporary object of `struct C` type,
  // calls the constructor for `C` on it, and returns it.
  private def factoryFunc(className: String, ctorAfunc: Afunc): Afunc = {
    val retTypeSpecs = new ListDeclaration_specifier
    retTypeSpecs.add(new Type(new Tstruct(new TagType(new Struct, className))))

    val ctorParams = ctorAfunc.function_def_
      .accept(getFunctionDeclaration, ())._2
      .accept(getDeclarator, ())
      .accept(getParameters, ())

    val objDecStm = {
      val specs = new ListDeclaration_specifier
      specs.add(new Type(new Tstruct(new TagType(new Struct, className))))
      val initDec = new ListInit_declarator
      initDec.add(new OnlyDecl(new NoPointer(new Name("__obj"))))
      new DecS(new Declarators(specs, initDec, new ListExtra_specifier))
    }

    val ctorCallStm = {
      val args = new ListExp
      args.add(new Epreop(new Address, new Evar("__obj")))
      ctorParams.forEach {
        case tap: TypeAndParam =>  args.add(new Evar(tap.accept(getName,())))
        case _                 =>
      }
      new ExprS(new SexprTwo(new Efunkpar(new Evar(className + "::ctor"), args)))
    }

    val bodyStms = new ListStm
    bodyStms.add(objDecStm)
    bodyStms.add(ctorCallStm)
    bodyStms.add(new JumpS(new SjumpFive(new Evar("__obj"))))

    new Afunc(
      new NewFunc(
        retTypeSpecs,
        new NoPointer(
          new NewFuncDec(
            new Name(factoryFuncName(className)),
            new AllSpec(ctorParams))),
        new ScompTwo(bodyStms)
    ))
  }

  override def visit(prog: Progr, arg: Any): Program = {
    val extDeclarations = new ListExternal_declaration

    // For each collected class:
    //  1. Create a global struct definition using its collected struct declarations
    //  2. Add collected member functions
    //  3. Add factory function using parameters from constructor
    for (className <- collectedDefs.keys) {
      val info = collectedDefs(className)
      extDeclarations.add(globalStruct(className, info.classDecs))
      info.classFuncs.foreach(f => extDeclarations.addLast(f.accept(this, ())))
      info.classFuncs
        .find(_.accept(getName, ()).endsWith("::ctor"))
        .foreach(ctor => extDeclarations.addLast(factoryFunc(className, ctor)))
    }

    // Process existing declarations
    for (decl <- prog.listexternal_declaration_.asScala) {
      val result = decl.accept(this, arg)

      // This condition skips declarations that define
      // classes but do not declare variables, since these must be removed
      if (result != null) extDeclarations.addLast(result)
    }

    val newProg = new Progr(extDeclarations)
    copyLocationInformation(prog, newProg)
  }


  // Creates a class object pointer to the parameters of a member function
  // off the form `struct className *this`
  private def structParam(className: String): Parameter_declaration = {
    val specs = new ListDeclaration_specifier
    specs.addFirst(new Type(new Tstruct(new TagType(new Struct, className))))
    new TypeAndParam(specs, new BeginPointer(new Point, new Name("this")))
  }

  private def fwdDecClassName(ident: String): String = {
    val idx = ident.lastIndexOf("::")
    val className =
      if (idx >= 0) ident.substring(0, idx)
      else ""
    className
  }

  // Adds `struct className *this` parameter to transformed member function definition
  override def visit(f: NewFuncDec, arg: Any): Direct_declarator = {
    val fullName = f.accept(getName, ())
    if (fullName.contains("::")) {
      val className = fwdDecClassName(fullName)
      val oldParams = f.parameter_type_.asInstanceOf[AllSpec].listparameter_declaration_
      val newParams = new ListParameter_declaration
      oldParams.forEach(_.accept(this, arg))
      newParams.addAll(oldParams)
      newParams.addFirst(structParam(className))
      copyLocationInformation(f, new NewFuncDec(f.direct_declarator_, new AllSpec(newParams)))
    }
    else f
  }

  // Adds `struct className *this` parameter to transformed member function definition
  override def visit(f: OldFuncDec, arg: Any): Direct_declarator = {
    val fullName = f.accept(getName, ())
    if (fullName.contains("::")) {
      val className = fwdDecClassName(fullName)
      val params = new ListParameter_declaration
      params.add(structParam(className))
      copyLocationInformation(f, new NewFuncDec(f.direct_declarator_, new AllSpec(params)))
    }
    else f
  }

  private def hasClassDef(d: Dec): Boolean = {
    val specs = d match {
      case nd:    NoDeclarator => nd.listdeclaration_specifier_
      case decls: Declarators  => decls.listdeclaration_specifier_
      case _                   => return false
    }
    specs.asScala.exists {
      case t: Type => t.type_specifier_.accept(isClass, ())
      case _ => false
    }
  }

  private def transformSpecifiers(decls: Declarators, arg: Any):
    (ListDeclaration_specifier, ListInit_declarator, ListExtra_specifier) = {
    val specs = new ListDeclaration_specifier
    decls.listdeclaration_specifier_.forEach {
      case t: Type if t.type_specifier_.accept(isClass, ()) =>
        // If type contains class definition, transform it to a struct TagType
        specs.add(new Type(new Tstruct(new TagType(new Struct, classNameFromTypeSpec(t.type_specifier_)))))
      case other => specs.add(other.accept(this, arg))
    }

    val initDecs = new ListInit_declarator
    decls.listinit_declarator_.forEach(id => initDecs.add(id.accept(this, arg)))

    val extraSpecs = new ListExtra_specifier
    decls.listextra_specifier_.forEach(e => extraSpecs.add(e.accept(this, arg)))

    (specs, initDecs, extraSpecs)
  }

  // Transforms a declaration of the form `class C {...} obj`
  // into one of the form `struct C obj`
  override def visit(g: Global, arg: Any): External_declaration = g.dec_ match {
    case nd: NoDeclarator if hasClassDef(nd) =>
      null
    case decls: Declarators if hasClassDef(decls) =>
      val (specs, initDecs, extraSpecs) = transformSpecifiers(decls, arg)
      copyLocationInformation(g, new Global(new Declarators(specs, initDecs, extraSpecs)))
    case _ =>
      copyLocationInformation(g, new Global(g.dec_.accept(this, arg)))
  }

  // Transforms a declaration of the form `class C {...} obj`
  // into one of the form `struct C obj`
  override def visit(d: DecS, arg: Any): DecS = d.dec_ match {
    case nd: NoDeclarator if hasClassDef(nd) =>
      null
    case decls: Declarators if hasClassDef(decls) =>
      val (specs, initDecs, extraSpecs) = transformSpecifiers(decls, arg)
      copyLocationInformation(d, new DecS(new Declarators(specs, initDecs, extraSpecs)))
    case _ =>
      copyLocationInformation(d, new DecS(d.dec_.accept(this, arg)))
  }


  // Transforms a call to a member function via a pointer from "Exp->funcName(...)" to "funcName(Exp, ...)"
  private def buildCallPoint(argExp: Exp, pointExp: Epoint, original: Exp, hasParams: Boolean): Exp = {
    val params = if (!hasParams) new ListExp else original.asInstanceOf[Efunkpar].listexp_
    params.addFirst(argExp)
    val newExp = new Efunkpar(new Evar(pointExp.cident_), params)
    copyLocationInformation(original, newExp.accept(this, ()))
  }

  // Transforms a call to a member function via a select from "Exp.funcName(...)" to "funcName(&Exp, ...)"
  private def buildCallSelect(argExp: Exp, selExp: Eselect, original: Exp, hasParams: Boolean): Exp = {
    val params = if (!hasParams) new ListExp else {
      val p = new ListExp
      original.asInstanceOf[Efunkpar].listexp_.forEach(e => p.add(e.accept(this, ())))
      p
    }
    val thisArg = new Epreop(new Address, argExp)
    params.addFirst(thisArg.accept(this, ()))
    val newExp = new Efunkpar(new Evar(selExp.cident_), params)
    copyLocationInformation(original, newExp)
  }

  // Dispatches the build functions for member function call sites
  private def transformCallTarget(targetExp: Exp, accessor: Exp, original: Exp, hasParams: Boolean): Option[Exp] = {
    val validTarget = targetExp.isInstanceOf[Eselect] || targetExp.isInstanceOf[Epoint] ||
                      targetExp.isInstanceOf[Evar]    || targetExp.isInstanceOf[EvarWithType]
    if (!validTarget) return None
    accessor match {
      case sel:   Eselect => Some(buildCallSelect(targetExp, sel,   original, hasParams))
      case point: Epoint  => Some(buildCallPoint (targetExp, point, original, hasParams))
      case _              => None
    }
  }

  // Finds calls to member functions of the form "Exp.funcName()" or "Exp->funcName()"
  // and transforms them as described in buildCall
  override def visit(exp: Efunk, arg: Any): Exp = exp.exp_ match {
    case sel:   Eselect => transformCallTarget(sel.exp_,   sel,   exp, hasParams = false).getOrElse(exp)
    case point: Epoint  => transformCallTarget(point.exp_, point, exp, hasParams = false).getOrElse(exp)
    case _              => exp
  }

  // Finds calls to member functions of the form "Exp.funcName(params)" or "Exp->funcName(params)"
  // and transforms them as described in buildCall
  override def visit(exp: Efunkpar, arg: Any): Exp = {
    val newArgs = new ListExp
    exp.listexp_.asScala.foreach(p => newArgs.add(p.accept(this, ())))
    val rebuilt = new Efunkpar(exp.exp_.accept(this, ()), newArgs)

    rebuilt.exp_ match {
      case sel:   Eselect => transformCallTarget(sel.exp_,   sel,   rebuilt, hasParams = true).getOrElse(rebuilt)
      case point: Epoint  => transformCallTarget(point.exp_, point, rebuilt, hasParams = true).getOrElse(rebuilt)
      case _              => rebuilt
    }
  }

  // Retrieves class name
  private def classNameFromDecl(decls: Declarators): String = {
    val types = new ListBuffer[Type_specifier]
    decls.listdeclaration_specifier_.forEach(_.accept(getType, types))
    types.collectFirst {
      case ts: Tstruct if ts.accept(isClass, ()) => ts.struct_or_union_spec_ match {
        case tagType: TagType => tagType.cident_
        case _ =>
          throw new ClassTransformException("Call to class constructor must be of type TagType")
      }
    }.getOrElse(throw new ClassTransformException("Class constructor isn't declared with a struct type"))
  }

  // Builds assignment to class object via call to its constructor
  private def buildConstructorDec(decls: Declarators, classCons: ClassCons): List[Stm] = {
    val className   = classNameFromDecl(decls)
    val objName     = classCons.accept(getName, ())
    val factoryArgs = new ListExp
    factoryArgs.add(classCons.exp_)
    val factoryCall = new Efunkpar(new Evar(factoryFuncName(className)), factoryArgs) // __create_className(args)
    val initDecs    = new ListInit_declarator
    initDecs.add(new InitDecl(new NoPointer(new Name(objName)), new InitExpr(factoryCall)))
    val newDec = new Declarators(copyAst(decls.listdeclaration_specifier_), initDecs, new ListExtra_specifier)
    List(new DecS(newDec.accept(this, ())))
  }

  // For declaration statements that direct initialize an object,
  // expand the statement to where the object is assigned to the result
  // from calling the factory function.
  //
  // Example:
  // class ClassName obj(args)
  //
  // gets turned into:
  // class ClassName obj = __create_ClassName(args);
  //
  private def expandStmt(stmt: Stm): List[Stm] = stmt match {
    case decS: DecS => decS.dec_ match {
      case decls: Declarators =>
        decls.listinit_declarator_.asScala.toList.flatMap { init =>
          val dirDec = init.accept(getDeclarator, ()) match {
            case d: BeginPointer => d.direct_declarator_
            case d: NoPointer    => d.direct_declarator_
          }
          dirDec match {
            case cons: ClassCons => buildConstructorDec(decls, cons)
            case _               => List(stmt.accept(this, ()))
          }
        }
      case _ => List(stmt.accept(this, ()))
}
    case _ => List(stmt.accept(this, ()))
  }

  override def visit(scomp: ScompTwo, arg: Any): ScompTwo = {
    val stmts = new ListStm
    scomp.liststm_.asScala.flatMap(expandStmt).foreach(stmts.add)
    copyLocationInformation(scomp, new ScompTwo(stmts))
  }

  // Retrieves class name
  private def classNameFromTypeSpec(ts: Type_specifier): String = {
    ts match {
      case s: Tstruct if ts.accept(isClass, ()) => s.struct_or_union_spec_ match {
        case t: TagType => t.cident_
        case t: Tag => t.cident_
        case _ => throw new ClassTransformException(s"Unsupported: Cannot retrieve class name for abstract class")
      }
      case _ => throw new ClassTransformException(s"Unsupported: Cannot retrieve class name non-class type")
    }
  }

  // Transforms constructor call expressions to call the factory function.
  // NOTE: Only works for class types, calling constructors of primitive types outside
  // of `new` expressions is not supported.
  override def visit(ctor: ECtor, arg: Any): Exp = {
    val className     = classNameFromTypeSpec(ctor.type_specifier_)
    val transformedArgs = new ListExp
    ctor.listexp_.forEach(e => transformedArgs.add(e.accept(this, ())))
    copyLocationInformation(ctor, new Efunkpar(new Evar(factoryFuncName(className)), transformedArgs))
  }

  // Turns a destructor call of the form `obj.~className()` into `className::dtor(&obj)`
  override def visit(dtor: ESelDtor, arg: Any): Exp = {
    val className = classNameFromTypeSpec(dtor.type_specifier_)
    val params    = new ListExp
    params.addFirst(new Epreop(new Address, dtor.exp_).accept(this, ()))
    copyLocationInformation(dtor, new Efunkpar(new Evar(className ++ "::dtor"), params))
  }

  // Turns a destructor call of the form `obj->~className()` into `className::dtor(obj)`
  override def visit(dtor: EPointDtor, arg: Any): Exp = {
    val className = classNameFromTypeSpec(dtor.type_specifier_)
    val params    = new ListExp
    params.addFirst(dtor.exp_.accept(this, ()))
    copyLocationInformation(dtor, new Efunkpar(new Evar(className ++ "::dtor"), params))
  }
}
