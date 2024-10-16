package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._

import scala.collection.mutable.{HashMap => MHashMap}
import scala.collection.JavaConverters._
import scala.collection.mutable.Stack

class TypeAnnotationException(msg : String) extends Exception(msg)

object CCAstTypeAnnotator {
  def apply(program: Program): Program = {
    val annotator = new CCAstTypeAnnotator
    annotator.annotate(program)
  }
}

class CCAstTypeAnnotator {
  def annotate(program: Program): Program = {
    val visitor = new CCAstTypeAnnotationVisitor
    program.accept(visitor, getPreloadedSymbolTable())
  }

  private def getPreloadedSymbolTable() = {
    def createDeclSpecifiers(tps: List[Type_specifier]) = {
      val declSpec = new ListDeclaration_specifier
      for (tp <- tps) {
        declSpec.add(new Type(tp))
      }
      declSpec
    }

    def createDeclaration(name: String, tps: List[Type_specifier]) = {
      CCAstDeclaration(createDeclSpecifiers(tps), new OnlyDecl(new NoPointer(new Name(name))))
    }

    def createPointerDeclaration(name: String, tps: List[Type_specifier]) = {
      CCAstDeclaration(createDeclSpecifiers(tps), new OnlyDecl(new BeginPointer(new Point, new Name(name))))
    }

    val symTab = new CCAstTypeAnnotationData
    symTab.put("assume", createDeclaration("assume", List(new Tint)))
    symTab.put("assert", createDeclaration("assert", List(new Tvoid)))
    symTab.put("malloc", createPointerDeclaration("malloc", List(new Tunsigned, new Tlong)))
    symTab
  }
}

object CCAstDeclaration {
  private val copyAst = new CCAstCopyVisitor
  private val getName = new CCAstGetNameVistor

  def apply(d: ListDeclaration_specifier, i: Init_declarator, e: ListExtra_specifier): CCAstDeclaration = {
    new CCAstDeclaration(d, i, e)
  }

  def apply(d: ListDeclaration_specifier, i: Init_declarator): CCAstDeclaration = {
    new CCAstDeclaration(d, i, new ListExtra_specifier)
  }
} 

class CCAstDeclaration(d: ListDeclaration_specifier, i: Init_declarator, e: ListExtra_specifier) {
  import CCAstDeclaration.{copyAst, getName}
  private val declarationSpecifiers: ListDeclaration_specifier = d
  private val initDeclarator: Init_declarator = i
  private val extraSpecifiers: ListExtra_specifier = e

  def toEvarWithType(): EvarWithType = {
    val decSpecs = copyAst(declarationSpecifiers)
    val initDec = initDeclarator.accept(copyAst, ())
    new EvarWithType(initDeclarator.accept(getName, ()), decSpecs, initDec);
  }

  def toGlobal(): Global = {
    val initDecls = new ListInit_declarator
    initDecls.add(initDeclarator.accept(copyAst, ()))
    new Global(new Declarators(
      copyAst(declarationSpecifiers),
      initDecls,
      new ListExtra_specifier))
  }
}

class CCAstTypeAnnotationData {
  private val globalVariables = MHashMap[String, CCAstDeclaration]()

  def put(name: String, declaration: CCAstDeclaration) = {
    globalVariables += (name -> declaration)
  }

  def get(name: String): Option[CCAstDeclaration] = {
    globalVariables.get(name)
  }
}

/*
  Vistor class to extract a name from a declaration or definition.
*/
class CCAstGetNameVistor extends AbstractVisitor[String, Unit] {
    /* External_declaration */
    override def visit(ext: Afunc, arg: Unit): String = { ext.function_def_.accept(this, arg) }
    override def visit(ext: Athread, arg: Unit): String = { ext.thread_def_.accept(this, arg) }
    override def visit(ext: Global, arg: Unit): String = { ext.dec_.accept(this, arg) }
    override def visit(ext: Chan, arg: Unit): String = { ext.chan_def_.accept(this, arg) }

    /* Function_def */
    override def visit(defn: AnnotatedFunc, arg: Unit): String = { defn.declarator_.accept(this, arg); }
    override def visit(defn: NewFuncInt, arg: Unit): String = { defn.declarator_.accept(this, arg); }
    override def visit(defn: NewFunc, arg: Unit): String = { defn.declarator_.accept(this, arg); }

    /* Thread_def */
    override def visit(trd: SingleThread, arg: Unit): String = { trd.cident_; }
    override def visit(trd: ParaThread, arg: Unit): String = { trd.cident_2; }

    /* Dec */
    override def visit(decs: Declarators, arg: Unit): String = {
      decs.listinit_declarator_.asScala.map(d => d.accept(this, arg)).filter(n => n != "").head
    }
    
    /* Init_declarator */
    override def visit(dec: OnlyDecl, arg: Unit): String = { dec.declarator_.accept(this, arg); }
    override def visit(dec: InitDecl, arg: Unit): String = { dec.declarator_.accept(this, arg); }
    override def visit(dec: HintDecl, arg: Unit): String = { dec.declarator_.accept(this, arg); }
    override def visit(dec: HintInitDecl, arg: Unit): String = { dec.declarator_.accept(this, arg); }

    /* Declarator */
    override def visit(dec: BeginPointer, arg: Unit): String = { return dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: NoPointer, arg: Unit): String = { return dec.direct_declarator_.accept(this, arg); }

    /* Direct_declarator */
    override def visit(dec: Name, arg: Unit): String = { return dec.cident_; }
    override def visit(dec: ParenDecl, arg: Unit): String = { return dec.declarator_.accept(this, arg); }
    override def visit(dec: InitArray, arg: Unit): String = { return dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: Incomplete, arg: Unit): String = { return dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: MathArray, arg: Unit): String = { return dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: NewFuncDec, arg: Unit): String = { return dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: OldFuncDec, arg: Unit): String = { return dec.direct_declarator_.accept(this, arg); }

    /* Parameter_declaration */
    override def visit(param: TypeAndParam, arg: Unit): String = { param.declarator_.accept(this, arg) }
    override def visit(param: TypeHintAndParam, arg: Unit): String = { param.declarator_.accept(this, arg) }
}

/*
  Vistor to copy an AST.
*/
class CCAstCopyVisitor extends ComposVisitor[Unit] {
  def apply(specifiers: ListDeclaration_specifier): ListDeclaration_specifier = {
    val decSpecifiers = new ListDeclaration_specifier
    for (d <- specifiers.asScala)
    {
      decSpecifiers.add(d.accept(this, ()));
    }
    decSpecifiers
  }

  def apply(specifiers: ListExtra_specifier): ListExtra_specifier = {
    val extraSpecifiers = new ListExtra_specifier
    for (s <- specifiers.asScala)
    {
      extraSpecifiers.add(s.accept(this, ()));
    }
    extraSpecifiers
  }

  def apply(expressions: ListExp) = {
    val expsCopy = new ListExp
    for (x <- expressions.asScala) {
      expsCopy.add(x.accept(this, ()))
    }
    expsCopy
  }
}

/*
  Vistor to extract a function declaration from a function definition.
*/
class CCAstGetFunctionDeclarationVistor extends AbstractVisitor[(ListDeclaration_specifier, Init_declarator), Unit] {
  val copyAst = new CCAstCopyVisitor
  /* Function_def */
  override def visit(defn: AnnotatedFunc, arg: Unit) = { 
    (copyAst(defn.listdeclaration_specifier_), new OnlyDecl(defn.declarator_.accept(copyAst, arg)));
  }
  override def visit(defn: NewFuncInt, arg: Unit) = {
    val declarationSpecifiers = new ListDeclaration_specifier
    declarationSpecifiers.add(new Type(new Tint))
    (declarationSpecifiers, new OnlyDecl(defn.declarator_.accept(copyAst, arg))); 
  }
  override def visit(defn: NewFunc, arg: Unit) = { 
    (copyAst(defn.listdeclaration_specifier_), new OnlyDecl(defn.declarator_.accept(copyAst, arg)));
  }
}

/*
  Vistor to create a copy of an AST with EvarWithType nodes substituted for
  Evar nodes.
*/
class CCAstTypeAnnotationVisitor extends ComposVisitor[CCAstTypeAnnotationData] {
  val getName = new CCAstGetNameVistor
  val copyAst = new CCAstCopyVisitor
  val getDeclaration = new CCAstGetFunctionDeclarationVistor
  val nameStack = Stack[String]()

  def getScopedName(name: String): String = {
    // A "scoped name" is an fully qualified identifier where each
    // part of the scope is separated by the US (unit separator)
    // character. The outer most scope is the first part etc.
    // This will never conflict with an identifier in the original
    // source since US is not a valid identifier character in C.
    if (nameStack.isEmpty) {
      name
    } else {
      nameStack.mkString("", "\u001F", "\u001F") + name
    }
  }

  def withScope[A](name: String)(thunk: => A): A = {
    nameStack.push(name)
    val result = thunk
    nameStack.pop()
    result
  } 

  /*
    Add an entry in the symbol table for the defined function.
    Parse the body in function name scope.
  */
  override def visit(func: Afunc, symTab: CCAstTypeAnnotationData): External_declaration = {
    val funcName = func.function_def_.accept(getName, ())
    val (decSpecifiers, initDeclarator) = func.function_def_.accept(getDeclaration, ())

    symTab.put(funcName, CCAstDeclaration(decSpecifiers, initDeclarator))

    withScope(funcName) {
      super.visit(func, symTab)
    }
  }

  /*
    Add an entry in the symbol table for each declaration
    in the statement.
  */
  override def visit(dec: Declarators, symTab: CCAstTypeAnnotationData): Dec = {
    // TODO: This will break symbol table entries when the declaration is shadowing
    //   another variable. This can be fixed by adding scope awareness, i.e. open a
    //   new "withScope" for each scope in the source.
    for (initDeclarator <- dec.listinit_declarator_.asScala)
    {
      val decSpecifiers = copyAst(dec.listdeclaration_specifier_)
      val extraSpecifiers = copyAst(dec.listextra_specifier_)
      val initDec = initDeclarator.accept(copyAst, ())
      val name = getScopedName(initDeclarator.accept(getName, ()))

      symTab.put(name, CCAstDeclaration(decSpecifiers, initDec, extraSpecifiers))
    }
    super.visit(dec, symTab)
  }

  override def visit(param: TypeAndParam, symTab: CCAstTypeAnnotationData): Parameter_declaration = {
    val name = getScopedName(param.declarator_.accept(getName, ()))
    val spec = copyAst(param.listdeclaration_specifier_)
    val decl = new OnlyDecl(param.declarator_.accept(copyAst, ()))
    symTab.put(name, CCAstDeclaration(spec, decl))
    super.visit(param, symTab)
  }

  override def visit(param: TypeHintAndParam, symTab: CCAstTypeAnnotationData): Parameter_declaration = {
    val name = getScopedName(param.declarator_.accept(getName, ()))
    val spec = copyAst(param.listdeclaration_specifier_)
    val decl = new OnlyDecl(param.declarator_.accept(copyAst, ()))
    symTab.put(name, CCAstDeclaration(spec, decl))
    super.visit(param, symTab)
  }

  /*
    Create an EvarWithType node for any Evar node.
  */
  override def visit(eVar: Evar, symTab: CCAstTypeAnnotationData): Exp = {
    def findDeclaration(name: String) = {
      symTab.get(getScopedName(name)) match {
        case None => symTab.get(name)
        case Some(declaration) => Some(declaration)
      }
    }

    val name = eVar.cident_
    findDeclaration(name) match {
      case None => 
        throw new TypeAnnotationException(f"Undeclared identifier in expression: ${name}")
      case Some(declaration) =>
        val newVar = declaration.toEvarWithType()
        newVar.col_num = eVar.col_num
        newVar.line_num = eVar.line_num
        newVar.offset = eVar.offset
        newVar
    }
  }
}
