package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._
import tricera.concurrency.CCAstUtils.isStackPtr

import scala.collection.mutable.{HashMap => MHashMap, MutableList}
import scala.util.{Try,Success,Failure}
import scala.collection.JavaConverters._
import scala.collection.mutable.Buffer

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
  Vistor class to replace one function declaration with another.
*/
class CCAstReplaceFunctionDeclarationVistor extends ComposVisitor[Direct_declarator] {
  /* Direct_declarator */
  override def visit(dec: NewFuncDec, replacement: Direct_declarator) = { replacement }
  override def visit(dec: OldFuncDec, replacement: Direct_declarator) = { replacement }
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
}

/*
  CallSiteTransform represents all the transforms that needs to be
  done of a specific function and at a specific call site in order
  to replace arguments pointing towards the stack (stack pointer
  arguments), with global variables.
*/
object CallSiteTransform {
  type CallSiteTransforms = MutableList[CallSiteTransform]
  private val copyAst = new CCAstCopyVisitor
  private val getDeclarator = new CCAstGetDeclaratorVistor
  private val getFunctionDeclaration = new CCAstGetFunctionDeclarationVistor
  private val getParameters = new CCAstGetParametersVistor
  private val getName = new CCAstGetNameVistor
  private val toName = new CCAstDeclaratorToNameVistor
  private val rename = new CCAstRenameInDeclarationVistor
  private val replaceFuncDec = new CCAstReplaceFunctionDeclarationVistor
  private val getFunctionBody = new CCAstGetFunctionBodyVistor
  private val removePointer = new CCAstRemovePointerLevelVistor
  private val toCCAstDeclaration = new CCAstParamToAstDeclarationVistor

  def apply(
    ptrTransformer: CCAstStackPtrArgToGlobalTransformer,
    funcDef: Function_def,
    args: ListExp): CallSiteTransform = {
    new CallSiteTransform(ptrTransformer, funcDef, copyAst(args))
  }

  private def wrapIdentifier(id: String) = {
    // We use the non-printable 0x1F US (Unit Separator)
    // as a means to get a new identifier name not colliding
    // with something existing in the original source.
    f"wrapped\u001F${id}"
  }

  private def transformIdentifier(id: String): String = { 
    f"global\u001F${id}" 
  }

  private def resultIdentifier(id: String): String = { 
    f"result\u001F${id}" 
  }

  private def toGlobalVariableName(functionName: String)(name: String) = {
    f"global\u001F${functionName}\u001F${name}"
  }
}

class CallSiteTransform(
  stackPtrTransformer:CCAstStackPtrArgToGlobalTransformer,
  originalDef: Function_def,
  args: ListExp) {
  import CallSiteTransform._

  private val (specifiers, declarator) = {
    val (spec, dec) = originalDef.accept(getFunctionDeclaration, ())
    (spec, dec.accept(getDeclarator, ()))
  }
  private val params = declarator.accept(getParameters, ())
  private val (keptParams, removedParams) = {
    val kept = new ListParameter_declaration
    val removed = new ListParameter_declaration
    val (r, k) = params.asScala.zip(args.asScala).partition({case (param, arg) => isStackPtr(arg)})
    r.map({case (param, arg) => param.accept(copyAst, ())}).foreach(param => removed.add(param))
    k.map({case (param, arg) => param.accept(copyAst, ())}).foreach(param => kept.add(param))
    (kept, removed)
  }
  private val keptArgs = {
    val kept = new ListExp
    args.asScala
    .withFilter(!isStackPtr(_))
    .foreach(param => kept.add(param.accept(copyAst, ())))
    kept
  }

  val originalFuncName = declarator.accept(getName, ())

  def getAstAdditions(): AstAddition = {
    val additions = new AstAddition
    accumulateAdditions(additions)
    additions
  }

  def wrapperInvocation(): Efunkpar = {
    new Efunkpar(wrapperDeclaration().toEvarWithType(), copyAst(args))
  }

  private def accumulateAdditions(knownAdditions: AstAddition):Unit = {
    val transDec = transformedDeclaration()
    if (!knownAdditions.transformedFunctionDefinitions.contains(transDec.getId())) {
      val wrapperDec = wrapperDeclaration()
      val (body, transforms) = createTransformedBody(originalDef.accept(getFunctionBody, ()))

      knownAdditions += AstAddition(
        wrapperDec.toGlobal(),
        wrapperDec.toAfunc(createWrapperBody()),
        transDec.toGlobal(),
        transDec.toAfunc(body),
        globalVariableDeclarations())

      transforms.foreach(t => t.accumulateAdditions(knownAdditions))
    }
  }

  private def transformedDeclaration() = {
    val funcDec = if (keptParams.size > 0) {
      new NewFuncDec(new Name(transformIdentifier(originalFuncName)), new AllSpec(copyAst(keptParams)))
    } else {
      new OldFuncDec(new Name(transformIdentifier(originalFuncName)))
    }
    CCAstDeclaration(
      copyAst(specifiers),
      new OnlyDecl(declarator.accept(replaceFuncDec, funcDec)))
  }

  private def createTransformedBody(originalBody: Compound_stm) = {
    val transforms = new CallSiteTransforms
    val paramToGlobalVar = removedParams.asScala.map(p => (p.accept(getName,()), toGlobalDeclaration(p))).toMap
    val transformedBody = 
      originalBody
        .accept(new CCAstPointerToGlobalVisitor, paramToGlobalVar)
        .accept(stackPtrTransformer, transforms)
    (transformedBody, transforms)
  }

  private def globalVariableDeclarations(): ListExternal_declaration = {
    val globals = new ListExternal_declaration
    for (param <- removedParams.asScala) {
      globals.add(toGlobalDeclaration(param).toGlobal())
    }
    globals
  }

  private def toGlobalDeclaration(param: Parameter_declaration) = {
    param
      .accept(rename, toGlobalVariableName(originalFuncName)(_))
      .accept(removePointer, ())
      .accept(toCCAstDeclaration, ())
  }

  private def wrapperDeclaration(): CCAstDeclaration = {
    val funcDec = if (params.size > 0) {
      new NewFuncDec(new Name(wrapIdentifier(originalFuncName)), new AllSpec(copyAst(params)))
    } else {
      new OldFuncDec(new Name(wrapIdentifier(originalFuncName)))
    }
    CCAstDeclaration(
      copyAst(specifiers),
      new OnlyDecl(declarator.accept(replaceFuncDec, funcDec)))
  }

  private def createWrapperBody(): Compound_stm = {
    def paramToGlobalAssignmentStm(param: CCAstDeclaration, global: CCAstDeclaration) = {
      new ExprS(new SexprTwo(new Eassign(
        global.toEvarWithType(),
        new Assign, 
        new Epreop(new Indirection(), param.toEvarWithType()))))
    }

    def globalToParamAssignmentStm(param: CCAstDeclaration, global: CCAstDeclaration) = {
      new ExprS(new SexprTwo(
          new Eassign(
            new Epreop(new Indirection(), param.toEvarWithType()),
            new Assign,
            global.toEvarWithType())))
    }

    def resultDeclaration(): Option[CCAstDeclaration] = {
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

    def transformedFunctionInvocationStm() = {
      val func = transformedDeclaration()
      val callExp = if (keptParams.size > 0) {
        new Efunkpar(func.toEvarWithType(), copyAst(keptArgs))
      } else {
        new Efunk(func.toEvarWithType())
      }

      val statement = resultDeclaration() match {
        case None => new ExprS(new SexprTwo(callExp))
        case Some(resultVar) =>
          new ExprS(new SexprTwo(new Eassign(resultVar.toEvarWithType(), new Assign, callExp)))
      }
      statement
    }

    def returnStm() = {
      resultDeclaration() match {
        case None => new JumpS(new SjumpFour())
        case Some(resultVar) => new JumpS(new SjumpFive(resultVar.toEvarWithType()))
      }
    }

    def composeBody() = {
      val pairs = removedParams.asScala.map(p => (p.accept(toCCAstDeclaration,()), toGlobalDeclaration(p)))
      val body = new ListStm
  
      resultDeclaration() match {
        case None => ;
        case Some(resultDeclaration) => body.add(new DecS(resultDeclaration.toDeclarators()))
      }

      // TODO: Add assignments to local variables to save the global state.
      //   Important if function is called recursively.
      for ((param, global) <- pairs) {
        body.add(paramToGlobalAssignmentStm(param, global))
      }
   
      body.add(transformedFunctionInvocationStm())
  
      for ((param, global) <- pairs.reverse) {
        body.add(globalToParamAssignmentStm(param, global))
      }
      // TODO: Add assignments from local variables to restore the global state.
      //   Important if function is called recursively.
  
      body.add(returnStm())
      body
    }

    new ScompTwo(composeBody())
  }
}

/*
  AstAddition contains all the additions that needs to be added
  to the AST in order for it to contain all functions and variables
  used by the program after stack pointers have been replaced.
*/
object AstAddition {
  private val getName = new CCAstGetNameVistor
  def apply(
    wrapperDeclaration: External_declaration,
    wrapperDefinition: External_declaration,
    transformedDeclaration: External_declaration,
    transformedDefinition: External_declaration,
    introducedGlobalVariables: ListExternal_declaration): AstAddition = {
    val addition = new AstAddition
    addition.transformedFunctionDefinitions.put(transformedDefinition.accept(getName, ()), transformedDefinition)
    addition.transformedFunctionDeclarations.put(transformedDeclaration.accept(getName, ()), transformedDeclaration)
    addition.wrapperDeclarations.put(wrapperDeclaration.accept(getName, ()), wrapperDeclaration)
    addition.wrapperDefinitions.put(wrapperDefinition.accept(getName, ()), wrapperDefinition)
    introducedGlobalVariables.asScala.foreach(g => addition.introducedGlobalVariables.put(g.accept(getName, ()), g))
    addition
  }
}

class AstAddition(
  val wrapperDeclarations: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val wrapperDefinitions: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val transformedFunctionDeclarations: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val transformedFunctionDefinitions: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val introducedGlobalVariables: MHashMap[String, External_declaration] = MHashMap[String, External_declaration]()) {

  def +(that: AstAddition) = {
    new AstAddition(
      this.wrapperDeclarations ++ that.wrapperDeclarations,
      this.wrapperDefinitions ++ that.wrapperDefinitions,
      this.transformedFunctionDeclarations ++ that.transformedFunctionDeclarations,
      this.transformedFunctionDefinitions ++ that.transformedFunctionDefinitions,
      this.introducedGlobalVariables ++ that.introducedGlobalVariables)
  }

  def +=(that: AstAddition) = {
    this.wrapperDeclarations ++= that.wrapperDeclarations
    this.wrapperDefinitions ++= that.wrapperDefinitions
    this.transformedFunctionDeclarations ++= that.transformedFunctionDeclarations
    this.transformedFunctionDefinitions ++= that.transformedFunctionDefinitions
    this.introducedGlobalVariables ++= that.introducedGlobalVariables
    this
  }
}


object  CCAstStackPtrArgToGlobalTransformer {
  import CallSiteTransform.CallSiteTransforms
  def apply(program: Program) = {
    val transformer = new CCAstStackPtrArgToGlobalTransformer
    program.accept(transformer, new CallSiteTransforms)
  }
}

class CCAstStackPtrArgToGlobalTransformer extends ComposVisitor[CallSiteTransform.CallSiteTransforms] {
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
  import CallSiteTransform.CallSiteTransforms

  private val getName = new CCAstGetNameVistor
  private val copyAst = new CCAstCopyVisitor
  private val rename = new CCAstRenameInDeclarationVistor
  private val functionDefinitions = new MHashMap[String, Function_def]

  /* Program */
  override def visit(progr: Progr, callSiteTransforms: CallSiteTransforms): Program = {
    def processExternalDeclarations(extDecl: ListExternal_declaration, transforms: CallSiteTransforms) = {
      val extDeclarations = new ListExternal_declaration
      for (x <- extDecl.asScala)
      {
        extDeclarations.add(x.accept(this, transforms));
      }
      extDeclarations
    }

    def isMainDefinition(dec: External_declaration): Boolean = dec match {
      case funcDef: Afunc if (funcDef.function_def_.accept(getName, ()) == "main") => true
      case _ => false
    }

    val declarations = processExternalDeclarations(progr.listexternal_declaration_, callSiteTransforms)
    val mainDefIndex = declarations.lastIndexOf(declarations.asScala.find(isMainDefinition(_)).get)

    val additions = callSiteTransforms.map(t => t.getAstAdditions()).reduce((a,b) => {a += b})

    declarations.addAll(mainDefIndex, additions.wrapperDefinitions.map(i => i._2).asJavaCollection)
    declarations.addAll(mainDefIndex, additions.transformedFunctionDefinitions.map(i => i._2).asJavaCollection)
    declarations.addAll(mainDefIndex, additions.wrapperDeclarations.map(i => i._2).asJavaCollection)
    declarations.addAll(mainDefIndex, additions.introducedGlobalVariables.map(i => i._2).asJavaCollection)

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
        val tform = CallSiteTransform(this, functionDefinitions(callSite.accept(getName, ())), callSite.listexp_)
        transforms += tform
        tform.wrapperInvocation()
    }
  }
}