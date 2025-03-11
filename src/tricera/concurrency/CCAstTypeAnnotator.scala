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

    //def createFunctionDeclaration(name: String, tps: List[Type_specifier], params: )

    // SSSOWO TODO: What about function arguments? Why don't we add them?
    val symTab = new CCAstTypeAnnotationData
    symTab.put("assume", createDeclaration("assume", List(new Tint)))
    symTab.put("assert", createDeclaration("assert", List(new Tvoid)))
    symTab.put("malloc", createPointerDeclaration("malloc", List(new Tunsigned, new Tlong)))
    symTab.put("calloc", createPointerDeclaration("calloc", List(new Tunsigned, new Tlong)))
    symTab.put("alloca", createPointerDeclaration("alloca", List(new Tunsigned, new Tlong)))
    symTab.put("free", createPointerDeclaration("free", List(new Tvoid)))
    symTab.put("reach_error", createPointerDeclaration("reach_error", List(new Tvoid)))
    symTab.put("chan_send", createPointerDeclaration("chan_send", List(new Tvoid)))
    symTab.put("chan_receive", createPointerDeclaration("chan_receive", List(new Tvoid)))
    symTab.put("__builtin_alloca", createPointerDeclaration("__builtin_alloca", List(new Tvoid)))
    symTab.put("realloc", createPointerDeclaration("realloc", List(new Tvoid)))
    symTab.put("static_assert", createPointerDeclaration("static_assert", List(new Tvoid)))
    symTab
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

/**
  Visitor to create a copy of an AST with EvarWithType nodes substituted for
  Evar nodes.
*/
class CCAstTypeAnnotationVisitor extends CCAstCopyWithLocation[CCAstTypeAnnotationData] {
  val getName = new CCAstGetNameVistor
  val copyAst = new CCAstCopyVisitor
  val getDeclaration = new CCAstGetFunctionDeclarationVistor
  val enumNameToEnumVar = new CCAstEnumNameToEnumVarVistor
  val nameStack = Stack[String]()
  val decSpecifiersStack = Stack[ListDeclaration_specifier]()

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

  def withDeclarationSpecifiers[A](decs: ListDeclaration_specifier)(thunk: => A): A = {
    decSpecifiersStack.push(decs)
    val result = thunk
    decSpecifiersStack.pop()
    result
  }

  def currentDecSpecifiers = decSpecifiersStack.top


  /**
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

  /**
    Add an entry in the symbol table for each defined channel.
  */
  override def visit(chan: AChan, symTab: CCAstTypeAnnotationData): Chan_def = {
    for (name_ <- chan.listcident_.asScala) {
      val decSpecifiers = new ListDeclaration_specifier
      val extraSpecifiers = new ListExtra_specifier
      val initDec = new OnlyDecl(new NoPointer(new Name(name_)))
      val name = getScopedName(name_)

      symTab.put(name, CCAstDeclaration(decSpecifiers, initDec, extraSpecifiers))
    }
    super.visit(chan, symTab)
  }

/**
  This is mainly for keeping track of the current declaration to enable
  correct types for enum members.
  */
  override def visit(dec: NoDeclarator, symTab: CCAstTypeAnnotationData): Dec = {
    withDeclarationSpecifiers(dec.listdeclaration_specifier_) {
      super.visit(dec, symTab)
    }
  }

  /**
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

    withDeclarationSpecifiers(dec.listdeclaration_specifier_) {
      super.visit(dec, symTab)
    }
  }

  /**
    Add an entry in the symbol table for each enum value in an enumeration.
  */
  override def visit(enum: EnumDec, symTab: CCAstTypeAnnotationData): Enum_specifier = {
    addEnumerators(enum.listenumerator_, symTab)
    super.visit(enum, symTab)
  }

  override def visit(enum: EnumName, symTab: CCAstTypeAnnotationData): Enum_specifier = {
    addEnumerators(enum.listenumerator_, symTab)
    super.visit(enum, symTab)
  }

  private def addEnumerators(enums: ListEnumerator, symTab: CCAstTypeAnnotationData): Unit = {
    enums.asScala.foreach(e => {
      val name = e.accept(getName, ())
      symTab.put(
        name, CCAstDeclaration(enumNameToEnumVar(currentDecSpecifiers),
        new OnlyDecl(new NoPointer(new Name(name)))))
    })
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

  /**
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
        throw new TypeAnnotationException(
          f"Undeclared identifier in expression: ${name}, line: ${eVar.line_num} col:${eVar.col_num}")
      case Some(declaration) =>
        val newVar = declaration.toEvarWithType()
        newVar.col_num = eVar.col_num
        newVar.line_num = eVar.line_num
        newVar.offset = eVar.offset
        newVar
    }
  }
}
