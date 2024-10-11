package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._

import scala.collection.mutable.MutableList
import scala.collection.JavaConverters._
import tricera.concurrency.ReaderMain.falseNodeId
import javax.xml.crypto.dsig.Transform
import tricera.params.TriCeraParameters

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
  Vistor class to rename a declaration or definition.
*/
class CCAstRenameInDeclarationVistor extends ComposVisitor[String => String] {
  /* Direct_declarator */
  override def visit(dec: Name, rename: String => String): Name = { new Name(rename(dec.cident_)) }
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

private object CCAstUtils {
  def isStackPtrInitialized(identifier: EvarWithType): Boolean = {
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

object CallSiteTransform {
  private val copyAst = new CCAstCopyVisitor
  private val getDeclarator = new CCAstGetDeclaratorVistor

  def apply(callSite: Efunkpar): CallSiteTransform = callSite.exp_ match {
    // TODO: This will not work if function is invoked through
    //   a pointer. Then we don't know the name of the function
    //   being invoked. Therefore we can't create/invoke a
    //   transformed function.
    case funcId: EvarWithType =>
      new CallSiteTransform(
        copyAst(funcId.listdeclaration_specifier_), 
        funcId.init_declarator_.accept(getDeclarator, ()),
        copyAst(callSite.listexp_))
    case _: Evar =>
      throw new CallSiteTransformationException(
        "Internal error. Evar should have been replaced with EvarWithType.")
    case _ =>
      throw new CallSiteTransformationException(
        "Arguments that are pointing to data on the stack is only supported in direct calls.")
  }

  private def wrapIdentifier(id: String) = {
    // We use the non-printable 0x1F US (Unit Separator)
    // as a means to get a new identifier name not colliding
    // with something existing in the original source.
    f"wrapped\u001F${id}"
  }
}

class CallSiteTransform(specifiers: ListDeclaration_specifier, declarator: Declarator, args: ListExp) {
  import CallSiteTransform._
  private val getName = new CCAstGetNameVistor
  private val rename = new CCAstRenameInDeclarationVistor
  private val getFunctionBody = new CCAstGetFunctionBodyVistor

  val originalName = declarator.accept(getName, ())

  def wrapperDef():External_declaration = {
    new Afunc(new NewFunc(copyAst(specifiers), declarator.accept(rename, wrapIdentifier(_)), createWrapperBody()))
  }

  def wrappedInvocation(): Efunkpar = {
    new Efunkpar(
      new EvarWithType(
        wrapIdentifier(originalName),
        copyAst(specifiers),
        new OnlyDecl(declarator.accept(rename, wrapIdentifier(_)))),
      copyAst(args))
  }

  def transformDef(original: Function_def): External_declaration = {
    def transformIdentifier(id: String): String = { f"global\u001F${id}" }
    new Afunc(
      new NewFunc(
        copyAst(specifiers),
        declarator.accept(rename, transformIdentifier(_)),
        createTransformedBody(original.accept(getFunctionBody, ()))))
  }

  def globalVariableDeclarations(): ListExternal_declaration = {
    new ListExternal_declaration
  }

  private def createWrapperBody(): Compound_stm = {
    new ScompOne
  }

  private def createTransformedBody(original: Compound_stm) = {
    new ScompOne
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
  //   functions, and a global variable for each stack pointer argument.
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

  val getName = new CCAstGetNameVistor

  /* Program */
  override def visit(progr: Progr, callSiteTransforms: CallSiteTransforms): Program = {
    def processExternalDeclarations(extDecl: ListExternal_declaration, callSiteTransforms: CallSiteTransforms) = {
      val extDeclarations = new ListExternal_declaration
      for (x <- extDecl.asScala)
      {
        extDeclarations.add(x.accept(this, callSiteTransforms));
      }
      extDeclarations
    }

    def transformFunctions(funcs: CallSiteTransforms): ListExternal_declaration = {
      new ListExternal_declaration
    }

    def isMainDefinition(dec: External_declaration): Boolean = dec match {
      case funcDef: Afunc if (funcDef.function_def_.accept(getName, ()) == "main") => true
      case _ => false
    }

    val declarations = processExternalDeclarations(progr.listexternal_declaration_, callSiteTransforms)
    val newFunctionDefs = transformFunctions(callSiteTransforms)
    val mainDef = declarations.asScala.find(e => isMainDefinition(e))
    val mainDefIndex = declarations.lastIndexOf(mainDef.get)
    declarations.addAll(mainDefIndex, newFunctionDefs)
    return new Progr(declarations);
  }

  override def visit(callSite: Efunkpar, transforms: CallSiteTransforms): Exp = {
    callSite.listexp_.asScala.find(CCAstUtils.isStackPtr) match {
      case None =>
        super.visit(callSite, transforms)
      case Some(_) => 
        val tform = CallSiteTransform(super.visit(callSite, transforms).asInstanceOf[Efunkpar])
        transforms += tform
        tform.wrappedInvocation()
    }
  }
}