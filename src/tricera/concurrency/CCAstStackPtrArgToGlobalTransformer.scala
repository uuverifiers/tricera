package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._

import scala.collection.mutable.{HashMap => MHashMap, MutableList}
import scala.collection.JavaConverters._

private object CCAstUtils {
  def isStackPtrInitialized(identifier: EvarWithType): Boolean = {
    def check(inializer: Initializer) = inializer match {
      case init: InitExpr => isStackPtr(init.exp_)
      case _ => false
    }
    identifier.init_declarator_ match {
      case dec: HintInitDecl => check(dec.initializer_)
      case dec: InitDecl => check(dec.initializer_)
      case _ => false
    }
  }

  def isStackPtr(exp: Exp): Boolean = {
    // NOTE: This is very simplistic in it's interpretation of
    //   what is considered a stack pointer. However, something
    //   more refined will require more exlaborate data flow
    //   analysis.
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

  private def savedIdentifier(id: String): String = { 
    f"saved\u001F${id}" 
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
  import CCAstUtils.isStackPtr

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
    def addAnnotationMarkers(str: String) = {
      import tricera.parsers.CommentPreprocessor.annotationMarker
      annotationMarker + str + annotationMarker
    }

    val transDec = transformedDeclaration()
    if (!knownAdditions.transformedFunctionDefinitions.contains(transDec.getId())) {
      val wrapperDec = wrapperDeclaration()
      val (body, transforms) = createTransformedBody(originalDef.accept(getFunctionBody, ()))

      knownAdditions += AstAddition(
        wrapperDec.toGlobal(),
        wrapperDec.toAfunc(createWrapperBody()),
        transDec.toGlobal(),
        transDec.toAfunc(addAnnotationMarkers("contract"), body),
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
      new ExprS(new SexprTwo(new Eassign(
        new Epreop(new Indirection(), param.toEvarWithType()),
        new Assign,
        global.toEvarWithType())))
    }

    def assignmentStm(lhs: CCAstDeclaration, rhs: CCAstDeclaration) = {
      new ExprS(new SexprTwo(new Eassign(
        lhs.toEvarWithType(),
        new Assign,
        rhs.toEvarWithType())))
    }

    def initStm(lhs: CCAstDeclaration, rhs: CCAstDeclaration) = {
      new DecS(lhs.toDeclarators(Some(new InitExpr(rhs.toEvarWithType()))))
    }

    def resultDeclaration(): Option[CCAstDeclaration] = {
      val getType = new CCAstGetTypeVisitor
      val types = new MutableList[Type_specifier]
      specifiers.asScala.foreach(s => s.accept(getType, types))
      types.contains(new Tvoid) match {
        case true => 
          None
        case false =>
          Some(CCAstDeclaration(
            copyAst(specifiers),
            new OnlyDecl(declarator.accept(toName, resultIdentifier(_)))))
      }
    }

    def transformedFunctionInvocationStm() = {
      val func = transformedDeclaration()
      val callExp = if (keptParams.size > 0) {
        val params = new ListExp
        params.addAll(
          keptParams
            .asScala.map(p => p.accept(toCCAstDeclaration, ()).toEvarWithType())
            .asJavaCollection)
        new Efunkpar(func.toEvarWithType(), params)
      } else {
        new Efunk(func.toEvarWithType())
      }

      val statement = resultDeclaration() match {
        case None => new ExprS(new SexprTwo(callExp))
        case Some(decl) =>
          new DecS(decl.toDeclarators(Some(new InitExpr(callExp))))
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
      val paramGlobalPairs = removedParams.asScala.map(p => (p.accept(toCCAstDeclaration,()), toGlobalDeclaration(p)))
      val savedGlobalPairs = paramGlobalPairs.map({ case (p, g) => (g.withId(savedIdentifier(g.getId())), g)})
      val body = new ListStm
  
      for ((saved, global) <- savedGlobalPairs) {
        // Store global variables on stack to allow for recursive
        // calls of the wrapper
        body.add(initStm(saved, global))
      }

      for ((param, global) <- paramGlobalPairs) {
        body.add(paramToGlobalAssignmentStm(param, global))
      }

      body.add(transformedFunctionInvocationStm())
  
      for ((param, global) <- paramGlobalPairs.reverse) {
        body.add(globalToParamAssignmentStm(param, global))
      }

      for ((saved, global) <- savedGlobalPairs.reverse) {
        body.add(assignmentStm(global, saved))
      }
  
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

    def isEntryPointDefinition(dec: External_declaration): Boolean = dec match {
      // TODO: Currently this scans for "main". This needs to be
      //   adapted with extra input to be able to inject the 
      //   content from '-m:entry-function-name' option in TriCera.
      case funcDef: Afunc if (funcDef.function_def_.accept(getName, ()) == "main") => true
      case _ => false
    }

    val declarations = processExternalDeclarations(progr.listexternal_declaration_, callSiteTransforms)
    val mainDefIndex = declarations.lastIndexOf(declarations.asScala.find(isEntryPointDefinition(_)).get)

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