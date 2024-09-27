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
    program.accept(visitor, new CCAstTypeAnnotationData)
  }
}

object CCAstDeclaration {
  def apply(d: ListDeclaration_specifier, i: Init_declarator, e: ListExtra_specifier): CCAstDeclaration = {
    new CCAstDeclaration(d, i, e)
  }
} 

class CCAstDeclaration(d: ListDeclaration_specifier, i: Init_declarator, e: ListExtra_specifier) {
  val declarationSpecifiers: ListDeclaration_specifier = d
  val initDeclarator: Init_declarator = i
  val extraSpecifiers: ListExtra_specifier = e
}

class CCAstTypeAnnotationData {
  private val globalVariables = MHashMap[String, Declarators]()

  def put(name: String, declaration: Declarators) = {
    globalVariables += (name -> declaration)
  }

  def get(name: String): Option[Declarators] = {
    globalVariables.get(name)
  }
}

class CCAstGetNameVistor extends AbstractVisitor[String, Unit] {
    /* Function_def */
    override def visit(defn: AnnotatedFunc, arg: Unit): String = { defn.declarator_.accept(this, arg); }
    override def visit(defn: NewFuncInt, arg: Unit): String = { defn.declarator_.accept(this, arg); }
    override def visit(defn: NewFunc, arg: Unit): String = { defn.declarator_.accept(this, arg); }

    /* Thread_def */
    override def visit(trd: SingleThread, arg: Unit): String = { trd.cident_; }
    override def visit(trd: ParaThread, arg: Unit): String = { trd.cident_2; }

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
}

class CCAstTypeAnnotationVisitor extends ComposVisitor[CCAstTypeAnnotationData] {
  val getName = new CCAstGetNameVistor
  val nameStack = Stack[String]()

  def getScopedName(name: String): String = {
     nameStack.mkString("", ".", ".") + name
  }

  def withScope[A](name: String)(thunk: => A): A = {
    nameStack.push(name)
    val result = thunk
    nameStack.pop()
    result
  } 

  /*
  override def visit(globalDec: Global, symTab: CCAstTypeAnnotationData): External_declaration = {
    val name = globalDec.dec_.accept(getName, ())
    symTab.put(name, globalDec.dec_)
    val dec = globalDec.dec_.accept(this, symTab);
    new Global(dec);
  }
  */

  override def visit(func: Afunc, symTab: CCAstTypeAnnotationData): External_declaration = {
    val funcName = func.function_def_.accept(getName, ())
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
    //   another variable. This can be fixed by adding scope awareness.
    for (initDec <- dec.listinit_declarator_.asScala)
    {
      val decSpecifiers = new ListDeclaration_specifier
      for (d <- dec.listdeclaration_specifier_.asScala)
      {
        decSpecifiers.add(d.accept(this, symTab));
      }

      val extraSpecifiers = new ListExtra_specifier
      for (e <- dec.listextra_specifier_.asScala)
      {
        extraSpecifiers.add(e.accept(this, symTab));
      }

      val initDecs = new ListInit_declarator
      initDecs.add(initDec.accept(this, symTab));

      val name = getScopedName(initDec.accept(getName, ()))
      symTab.put(name, new Declarators(decSpecifiers, initDecs, extraSpecifiers))  
    }
    super.visit(dec, symTab)
  }

  override def visit(param: TypeAndParam, symTab: CCAstTypeAnnotationData): Parameter_declaration = {
    val name = getScopedName(param.declarator_.accept(getName, ()))
    
    symTab.put(name, param.declarator_)
    super.visit(param, symTab)
  }

  override def visit(param: TypeHintAndParam, symTab: CCAstTypeAnnotationData): Parameter_declaration = {
    val name = getScopedName(param.declarator_.accept(getName, ()))
    symTab.put(name, param.declarator_)
    super.visit(param, symTab)
  }

  /*
  override def visit(func: Efunkpar, symTab: CCAstTypeAnnotationData): Exp = {
    val f = func.exp_.accept(this, symTab)
    
    val args = new ListExp
    for (arg <- func.listexp_.asScala) {
      args.add(arg.accept(this,symTab))
    }
    new Efunkpar(f, args)
  }
  */

  /*
    Create an EvarWithType node for any Evar node.
  */
  override def visit(eVar: Evar, symTab: CCAstTypeAnnotationData): Exp = {
      def createEvarWithType(name: String, declaration: Declarators): EvarWithType = {
        val decSpecs = new ListDeclaration_specifier
        for (x <- declaration.listdeclaration_specifier_.asScala) {
          decSpecs.add(x.accept(this, symTab));
        }
  
        val initDecs = new ListInit_declarator
        for (x <- declaration.listinit_declarator_.asScala) {
          initDecs.add(x.accept(this, symTab));
        }
        new EvarWithType(name, decSpecs, initDecs);
      }

      val name = getScopedName(eVar.cident_)
      symTab.get(name) match {
        case None => 
          throw new TypeAnnotationException(f"Undeclared variable in expression: ${name}")
        case Some(declaration) =>
          createEvarWithType(name, declaration)
      }
  }
}
