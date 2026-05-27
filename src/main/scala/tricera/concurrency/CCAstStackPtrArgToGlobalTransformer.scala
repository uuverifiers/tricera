/**
 * Copyright (c) 2025 Scania CV AB. All rights reserved.
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
import concurrent_c.Absyn._

import scala.collection.mutable.{HashMap => MHashMap, ListBuffer}
import scala.jdk.CollectionConverters._

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

/**
  * Vistor to test if an expression is a pointer to stack allocated data.
  * 
  * NOTE: This visitor requires a type annotated AST as produced by
  *   the CCAstTypeAnnotationVistor.
  * 
  * NOTE: This is very simplistic in it's interpretation of
  *   what is considered a stack pointer. However, something
  *   more refined will require more elaborate data flow
  *   analysis.
  */
class CCAstIsStackPointerVisitor extends AbstractVisitor[Boolean, Unit] {
  /* Init_declarator */
  override def visit(dec: InitDecl, arg: Unit) = { dec.initializer_.accept(this, ()) }
  override def visit(dec: HintInitDecl, arg: Unit) = { dec.initializer_.accept(this, ()) }
  override def visitDefault(dec: Init_declarator, arg: Unit) = { false }

  /* Initializer */
  override def visit(init: InitExpr, arg: Unit) = { init.exp_.accept(this, ()) }
  override def visitDefault(init: Initializer, arg: Unit) = { false }

  /* Exp */
  override def visit(exp: Epreop, arg: Unit) = { exp.unary_operator_.accept(this, ()) }
  override def visit(exp: EvarWithType, arg: Unit) = { exp.init_declarator_.accept(this, ()) }
  override def visitDefault(exp: Exp, arg: Unit) = { false }

  /* Unary opperator */
  override def visit(op: Address, arg: Unit) = { true }
  override def visitDefault(op: Unary_operator, arg: Unit) = { false }
}

/** 
  * Vistor to replace given pointers with global variables.
  */
class CCAstPointerToGlobalVisitor extends CCAstCopyWithLocation[Map[String, CCAstDeclaration]] {
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

/**
  * CallSiteTransform represents all the transforms that needs to be
  * done of a specific function and at a specific call site in order
  * to replace arguments pointing towards the stack (stack pointer
  * arguments), with global variables.
  */
object CallSiteTransform {
  type CallSiteTransforms = ListBuffer[CallSiteTransform]
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

  // We use the non-printable 0x1F US (Unit Separator)
  // as a means to get a new identifier name not colliding
  // with something existing in the original source.
  private val separator = "\u001F"

  def apply(
    ptrTransformer: CCAstStackPtrArgToGlobalTransformer,
    funcDef: Function_def,
    args: ListExp): CallSiteTransform = {
    new CallSiteTransform(ptrTransformer, funcDef, copyAst(args))
  }
}

class CallSiteTransform(
  stackPtrTransformer:CCAstStackPtrArgToGlobalTransformer,
  originalDef: Function_def,
  args: ListExp) {
  import CallSiteTransform._
  import CCAstUtils.isStackPtr

  private val getAnnotations = new CCAstGetFunctionAnnotationVisitor

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

  val originalFuncName = declarator.accept(getName, ())
  val suffix = {
    args.asScala.zipWithIndex
      .withFilter({ case (arg, index) => isStackPtr(arg)})
      .map({ case (arg, index) => f"_${index}"})
      .reduce((a,b) => a+b)      
  }

  def getAstAdditions(): AstAddition = {
    val additions = new AstAddition
    accumulateAdditions(additions)
    additions
  }

  def wrapperInvocation(): Efunkpar = {
    new Efunkpar(wrapperDeclaration().toEvarWithType(), copyAst(args))
  }

  def shouldInferContract()
    : Boolean = getAnnotations(originalDef)
      .asScala.toList.map({case a: Annot1 => a.annotationstring_}) match {
        case head::tail if (head == addAnnotationMarkers("contract")) => true
        case _ => false
    }

  private def wrapIdentifier(id: String) = {
    f"wrapped${separator}${id}${suffix}"
  }

  private def transformIdentifier(id: String): String = { 
    f"global${separator}${id}${suffix}" 
  }

  private def resultIdentifier(id: String): String = { 
    f"result${separator}${id}${suffix}" 
  }

  private def savedIdentifier(id: String): String = { 
    f"saved${separator}${id}${suffix}" 
  }

  private def toGlobalVariableName(functionName: String)(name: String) = {
    f"global${separator}${functionName}${suffix}${separator}${name}"
  }

  private def addAnnotationMarkers(str: String) = {
    import tricera.parsers.CommentPreprocessor.annotationMarker
      annotationMarker + str + annotationMarker
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
        transDec.toAfunc(
          if (shouldInferContract()) {addAnnotationMarkers("contract")} else {""},
          body),
        globalVariableDeclarations(),
        globalVariableIdsToParameterIds(),
        MHashMap((transDec.getId() -> originalFuncName)),
        MHashMap((originalFuncName -> params.asScala.map(p => p.accept(getName,())).toList))
      )

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

  private def globalVariableIdsToParameterIds() = {
    val mapping = new MHashMap[String, String]
    removedParams.asScala.foreach(p => mapping.put(toGlobalDeclaration(p).getId(), p.accept(getName,())))
    mapping
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
      val types = new ListBuffer[Type_specifier]
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

      // TODO: If the original function returns some pointer it
      //   got as an argument, and that pointer is a stack pointer,
      //   this return value breaks. In such a case the original
      //   function would return the pointer to the stack, but this
      //   one will return the address of the global variable
      //   replacing the stack pointer.
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
        // Store global variables on the stack to allow for recursive
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

/**
  * AstAddition contains all the additions that needs to be added
  * to the AST in order for it to contain all functions and variables
  * used by the program after stack pointers have been replaced.
  */
object AstAddition {
  private val getName = new CCAstGetNameVistor
  def apply(
    wrapperDeclaration: External_declaration,
    wrapperDefinition: External_declaration,
    transformedDeclaration: External_declaration,
    transformedDefinition: External_declaration,
    introducedGlobalVariables: ListExternal_declaration,
    globalVariableIdToParameterId: MHashMap[String, String],
    transformedFunctionIdToOriginalId: MHashMap[String, String],
    originalFunctionIdToParamterIds: MHashMap[String, List[String]]): AstAddition = {
    val addition = new AstAddition
    addition.transformedFunctionDefinitions.put(transformedDefinition.accept(getName, ()), transformedDefinition)
    addition.transformedFunctionDeclarations.put(transformedDeclaration.accept(getName, ()), transformedDeclaration)
    addition.wrapperDeclarations.put(wrapperDeclaration.accept(getName, ()), wrapperDeclaration)
    addition.wrapperDefinitions.put(wrapperDefinition.accept(getName, ()), wrapperDefinition)
    introducedGlobalVariables.asScala.foreach(g => addition.introducedGlobalVariables.put(g.accept(getName, ()), g))
    addition.globalVariableIdToParameterId ++= globalVariableIdToParameterId
    addition.transformedFunctionIdToOriginalId ++= transformedFunctionIdToOriginalId
    addition.originalFunctionIdToParamterIds ++= originalFunctionIdToParamterIds
    addition
  }
}

class AstAddition(
  val wrapperDeclarations: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val wrapperDefinitions: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val transformedFunctionDeclarations: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val transformedFunctionDefinitions: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val introducedGlobalVariables: MHashMap[String, External_declaration] = MHashMap[String, External_declaration](),
  val globalVariableIdToParameterId: MHashMap[String, String] = MHashMap[String, String](),
  val transformedFunctionIdToOriginalId: MHashMap[String, String] = MHashMap[String, String](),
  val originalFunctionIdToParamterIds: MHashMap[String, List[String]] = MHashMap[String, List[String]]()) {

  def +(that: AstAddition) = {
    new AstAddition(
      this.wrapperDeclarations ++ that.wrapperDeclarations,
      this.wrapperDefinitions ++ that.wrapperDefinitions,
      this.transformedFunctionDeclarations ++ that.transformedFunctionDeclarations,
      this.transformedFunctionDefinitions ++ that.transformedFunctionDefinitions,
      this.introducedGlobalVariables ++ that.introducedGlobalVariables,
      this.globalVariableIdToParameterId ++ that.globalVariableIdToParameterId,
      this.transformedFunctionIdToOriginalId ++ that.transformedFunctionIdToOriginalId,
      this.originalFunctionIdToParamterIds ++ that.originalFunctionIdToParamterIds)
  }

  def +=(that: AstAddition) = {
    this.wrapperDeclarations ++= that.wrapperDeclarations
    this.wrapperDefinitions ++= that.wrapperDefinitions
    this.transformedFunctionDeclarations ++= that.transformedFunctionDeclarations
    this.transformedFunctionDefinitions ++= that.transformedFunctionDefinitions
    this.introducedGlobalVariables ++= that.introducedGlobalVariables
    this.globalVariableIdToParameterId ++= that.globalVariableIdToParameterId
    this.transformedFunctionIdToOriginalId ++= that.transformedFunctionIdToOriginalId
    this.originalFunctionIdToParamterIds ++= that.originalFunctionIdToParamterIds
    this
  }
}


object  CCAstStackPtrArgToGlobalTransformer {
  import CallSiteTransform.CallSiteTransforms
  def apply(program: Program, entryFunctionId: String) = {
    val transformer = new CCAstStackPtrArgToGlobalTransformer(entryFunctionId)
    val transforms = new CallSiteTransforms
    val transformedProg = program.accept(transformer, transforms)
    (transformedProg, transforms)
  }
}

class CCAstStackPtrArgToGlobalTransformer(val entryFunctionId: String)
  extends CCAstCopyWithLocation[CallSiteTransform.CallSiteTransforms] {
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
  private val fillFuncDefs = new CCAstFillFuncDef
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
      case funcDef: Afunc if (funcDef.function_def_.accept(getName, ()) == entryFunctionId) => true
      case _ => false
    }

    progr.accept(fillFuncDefs, functionDefinitions)
    val declarations = processExternalDeclarations(progr.listexternal_declaration_, callSiteTransforms)

    if (callSiteTransforms.nonEmpty) {
      val additions = callSiteTransforms.map(t => t.getAstAdditions()).reduce((a,b) => {a += b})
      
      val getMaxLineNumber = new CCAstMaxLineNumber
      val updateLineNumbers = new CCAstUpdtLineNum[Unit](
        declarations.asScala
          .map(d => d.accept(getMaxLineNumber, ()))
          .reduce(math.max)+1)
      val mainDefIndex = declarations.lastIndexOf(declarations.asScala.find(isEntryPointDefinition(_)).get)
      declarations.addAll(mainDefIndex, additions.introducedGlobalVariables
        .map(i => i._2)
        .map(i => {i.accept(updateLineNumbers, ()); i}).asJavaCollection)
      declarations.addAll(mainDefIndex, additions.wrapperDeclarations
        .map(i => i._2)
        .map(i => {i.accept(updateLineNumbers, ()); i}).asJavaCollection)
      declarations.addAll(mainDefIndex, additions.wrapperDefinitions
        .map(i => i._2)
        .map(i => {i.accept(updateLineNumbers, ()); i}).asJavaCollection)
      declarations.addAll(mainDefIndex, additions.transformedFunctionDefinitions
        .map(i => i._2)
        .map(i => {i.accept(updateLineNumbers, ()); i}).asJavaCollection)
      new Progr(declarations);
    } else {
      progr
    }
  }
  

  override def visit(callSite: Efunkpar, transforms: CallSiteTransforms): Exp = {
    (callSite.listexp_.asScala.find(CCAstUtils.isStackPtr),
     functionDefinitions.get(callSite.accept(getName, ()))) match {
      case (Some(_), Some(funcDef)) => 
        val exp = super.visit(callSite, transforms)
        // TODO: This will not work if function is invoked through
        //   a pointer. Then we don't know the name of the function
        //   being invoked. Therefore we can't create/invoke a
        //   transformed function.
        val tform = CallSiteTransform(this, funcDef, callSite.listexp_)
        if (tform.shouldInferContract()) {
          transforms += tform
          tform.wrapperInvocation()
        } else {
          exp
        }
      case (Some(_), None) =>
        // We are missing the function definition for the function
        // at the callsite. This could be either because it is a
        // library function or because it is a predicate defined in
        // $...$ comment syntax used as argument to assume/assert.
        // Either way we can't transform and rewrite the function.
        super.visit(callSite, transforms) 
      case _ =>
        super.visit(callSite, transforms)
    }
  }
}