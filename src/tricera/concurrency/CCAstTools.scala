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

import scala.collection.JavaConverters._
import scala.collection.mutable.{MutableList}

/**
  * This trait defines a function to set the line number of
  * an arbitrary kind of node in an AST.
  */
trait SetLineNumber {
  def setLineNumber[T](item: T, lineNumber: Int): Unit = {
    val field =  "line_num"
    item.getClass.getDeclaredField(field).setInt(item, lineNumber)
  }
}

/**
  * This trait defines a function to get the line number of
  * an arbitrary kind of node in an AST.
  */
trait GetLineNumber {
  def getLineNumber[T](item: T): Int = {
    val field =  "line_num"
    item.getClass.getDeclaredField(field).getInt(item)
  }
}

/**
  * The CCAstDeclaration represents a declaration in the AST.
  * It can be used to construct various kinds of nodes when
  * manipulating the tree.
  */
object CCAstDeclaration {
  private val copyAst = new CCAstCopyVisitor
  private val getName = new CCAstGetNameVistor
  private val getDeclarator = new CCAstGetDeclaratorVistor
  private val rename = new CCAstRenameInDeclarationVistor
  private val replaceInit = new CCAstReplaceInitializerVistor

  def apply(d: ListDeclaration_specifier, i: Init_declarator, e: ListExtra_specifier): CCAstDeclaration = {
    new CCAstDeclaration(d, i, e)
  }

  def apply(d: ListDeclaration_specifier, i: Init_declarator): CCAstDeclaration = {
    new CCAstDeclaration(d, i, new ListExtra_specifier)
  }
} 

class CCAstDeclaration(d: ListDeclaration_specifier, i: Init_declarator, e: ListExtra_specifier) {
  import CCAstDeclaration._
  private val declarationSpecifiers: ListDeclaration_specifier = d
  private val initDeclarator: Init_declarator = i
  private val extraSpecifiers: ListExtra_specifier = e

  def getId(): String = {
    initDeclarator.accept(getName, ())
  }

  def toAfunc(body: Compound_stm):Afunc = toAfunc("", body)

  def toAfunc(annotation: String, body: Compound_stm): Afunc = {
    annotation.isEmpty || annotation.isBlank match {
      case true =>
        new Afunc(
          new NewFunc(
            copyAst(declarationSpecifiers),
            initDeclarator.accept(getDeclarator, ()),
            body))
      case false => 
        val annotations = new ListAnnotation
        annotations.add(new Annot1(annotation))
        new Afunc(
          new AnnotatedFunc(
            annotations,
            copyAst(declarationSpecifiers),
            initDeclarator.accept(getDeclarator, ()),
            body)) 
    }
  }

  def toDeclarators(initializer: Option[Initializer] = None): Declarators = {
    val initDecls = new ListInit_declarator
    initializer match {
      case Some(_) => initDecls.add(initDeclarator.accept(replaceInit, initializer))
      case None => false
    }
    
    new Declarators(
      copyAst(declarationSpecifiers),
      initDecls,
      copyAst(e))
  }

  def toDeclarators(): Declarators = {
    val initDecls = new ListInit_declarator
    initDecls.add(initDeclarator.accept(copyAst, ()))
    new Declarators(
      copyAst(declarationSpecifiers),
      initDecls,
      copyAst(e))
  }

  def toEvarWithType(): EvarWithType = {
    val decSpecs = copyAst(declarationSpecifiers)
    val initDec = initDeclarator.accept(copyAst, ())
    new EvarWithType(initDeclarator.accept(getName, ()), decSpecs, initDec);
  }

  def toGlobal(): Global = {
    new Global(toDeclarators())
  }

  def withId(id: String) = {
    CCAstDeclaration(copyAst(declarationSpecifiers), initDeclarator.accept(rename, onlyRename(getId(), id)(_)))
  }

  private def onlyRename(oldId: String, newId: String)(testId: String) = {
    testId match {
        case `oldId` => newId
        case _ => oldId
    }
  }
}

/**
  * Vistor class to extract a name from a declaration or definition.
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

    /* Enumerator */
    override def visit(enum: Plain, arg: Unit): String = { enum.cident_ }
    override def visit(enum: EnumInit, arg: Unit): String = { enum.cident_ }

    /* Declarator */
    override def visit(dec: BeginPointer, arg: Unit): String = { dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: NoPointer, arg: Unit): String = { dec.direct_declarator_.accept(this, arg); }

    /* Direct_declarator */
    override def visit(dec: Name, arg: Unit): String = { dec.cident_; }
    override def visit(dec: ParenDecl, arg: Unit): String = { dec.declarator_.accept(this, arg); }
    override def visit(dec: InitArray, arg: Unit): String = { dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: Incomplete, arg: Unit): String = { dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: MathArray, arg: Unit): String = { dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: NewFuncDec, arg: Unit): String = { dec.direct_declarator_.accept(this, arg); }
    override def visit(dec: OldFuncDec, arg: Unit): String = { dec.direct_declarator_.accept(this, arg); }

    /* Parameter_declaration */
    override def visit(param: TypeAndParam, arg: Unit): String = { param.declarator_.accept(this, arg) }
    override def visit(param: TypeHintAndParam, arg: Unit): String = { param.declarator_.accept(this, arg) }

    /* Exp */
    override def visit(exp: Earray, arg: Unit) : String = { exp.exp_1.accept(this, ()) }
    override def visit(exp: Efunk, arg: Unit): String = { exp.exp_.accept(this, ()) }
    override def visit(exp: Efunkpar, arg: Unit): String = { exp.exp_.accept(this, ()) }
    override def visit(exp: Evar, arg: Unit): String = { exp.cident_ }
    override def visit(exp: EvarWithType, arg: Unit): String = { exp.cident_ }
}

/**
  * Vistor to copy an AST including source information.
  */
class CCAstCopyVisitor extends CCAstCopyWithLocation[Unit] {
  def apply(annotations: ListAnnotation): ListAnnotation = {
    val copy = new ListAnnotation
    copy.addAll(annotations.asScala.map(a => a.accept(this, ())).asJava)
    copy
  }

  def apply(specifiers: ListDeclaration_specifier): ListDeclaration_specifier = {
    val copy = new ListDeclaration_specifier
    copy.addAll(specifiers.asScala.map(s => s.accept(this, ())).asJava)
    copy
  }

  def apply(specifiers: ListExtra_specifier): ListExtra_specifier = {
    val copy = new ListExtra_specifier
    copy.addAll(specifiers.asScala.map(s => s.accept(this, ())).asJava);
    copy
  }

  def apply(expressions: ListExp) = {
    val copy = new ListExp
    copy.addAll(expressions.asScala.map(x => x.accept(this, ())).asJava)
    copy
  }

  def apply(params: ListParameter_declaration) = {
    val copy = new ListParameter_declaration
    copy.addAll(params.asScala.map(p => p.accept(this, ())).asJava)
    copy
  }
}

/**
  * Vistor to extract a function declaration from a function definition.
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

/**
  * Vistor to extract a function annotation from a function definition.
  */
class CCAstGetFunctionAnnotationVisitor extends AbstractVisitor[ListAnnotation, Unit] {
  val copyAst = new CCAstCopyVisitor

  def apply(defn: Function_def) = defn.accept(this, ())

  /* Function_def */
  override def visit(defn: AnnotatedFunc, arg: Unit) = { copyAst(defn.listannotation_) }
  override def visit(defn: NewFuncInt, arg: Unit) = { copyAst(defn.listannotation_) }
  override def visit(defn: NewFunc, arg: Unit) = { new ListAnnotation }
}

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


/**
  * Vistor class to remove one level of indirection ("dereference a pointer").
  */
class CCAstRemovePointerLevelVistor extends CCAstCopyWithLocation[Unit] {
  private val copyAst = new CCAstCopyVisitor

  /* Declarator */
  override def visit(dec: BeginPointer, arg: Unit): Declarator = { 
    dec.pointer_ match {
      case p: Point =>
        new NoPointer(dec.direct_declarator_.accept(copyAst, ()))
      case p: PointQual =>
        new NoPointer(dec.direct_declarator_.accept(copyAst, ()))
      case p: PointPoint =>
        new BeginPointer(
          p.pointer_.accept(copyAst, ()),
          dec.direct_declarator_.accept(copyAst, ()))
      case p: PointQualPoint =>
        new BeginPointer(
          p.pointer_.accept(copyAst, ()),
          dec.direct_declarator_.accept(copyAst, ()))
    }
  }
}

/**
  * Vistor class to rename a declaration or definition.
  */
class CCAstRenameInDeclarationVistor extends CCAstCopyWithLocation[String => String] {
  /* Direct_declarator */
  override def visit(dec: Name, rename: String => String): Name = { new Name(rename(dec.cident_)) }
}

/**
  * Vistor class to transform any declaration to a scalar variable declaration,
  * removing e.g. array or function declaration elements.
  */
class CCAstDeclaratorToNameVistor extends CCAstCopyWithLocation[String => String] {
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

/**
  * Vistor class to replace one function declaration with another.
  */
class CCAstReplaceFunctionDeclarationVistor extends CCAstCopyWithLocation[Direct_declarator] {
  /* Direct_declarator */
  override def visit(dec: NewFuncDec, replacement: Direct_declarator) = { replacement }
  override def visit(dec: OldFuncDec, replacement: Direct_declarator) = { replacement }
}

/**
  * Vistor class to replace one initialization with another.
  */
class CCAstReplaceInitializerVistor extends CCAstCopyWithLocation[Option[Initializer]] {
  private val copyAst = new CCAstCopyVisitor

  /* Init_declarator */
  override def visit(dec: OnlyDecl, replacement: Option[Initializer]): Init_declarator = { 
    replacement match {
        case None => new OnlyDecl(dec.declarator_.accept(copyAst, ()))
        case Some(init) => new InitDecl(dec.declarator_.accept(copyAst, ()), init)
    } 
  }

  override def visit(dec: InitDecl, replacement: Option[Initializer]): Init_declarator = {
    replacement match {
        case None => new OnlyDecl(dec.declarator_.accept(copyAst, ()))
        case Some(init) => new InitDecl(dec.declarator_.accept(copyAst, ()), init)
    } 
  }
  
  override def visit(dec: HintDecl, replacement: Option[Initializer]): Init_declarator = {
    replacement match {
        case None => new HintDecl(
          copyAst(dec.listannotation_),
          dec.declarator_.accept(copyAst, ()))
        case Some(init) => new HintInitDecl(
          copyAst(dec.listannotation_),
          dec.declarator_.accept(copyAst, ()),
          init)
    }
  }
  
  override def visit(dec: HintInitDecl, replacement: Option[Initializer]): Init_declarator = {
    replacement match {
        case None => new HintDecl(
          copyAst(dec.listannotation_),
          dec.declarator_.accept(copyAst, ()))
        case Some(init) => new HintInitDecl(
          copyAst(dec.listannotation_),
          dec.declarator_.accept(copyAst, ()),
          init)
    }
  }
}

/**
  * Vistor to extract a function body from a function definition.
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

/**
  * Vistor to extract the "Parameter_type" part from a Declarator
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

/**
  * Vistor to convert function parameters to CCAstDeclaration.
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

/**
  * Vistor to get declared type from a specifier.
  */
class CCAstGetTypeVisitor extends AbstractVisitor[Boolean, MutableList[Type_specifier]] {
  /* Declaration_specifier */
  override def visit(spec: Type, types: MutableList[Type_specifier]) = { types += spec.type_specifier_; true }
  override def visit(spec: Storage, types: MutableList[Type_specifier]) = { false }
  override def visit(spec: SpecProp, types: MutableList[Type_specifier]) = { false }
  override def visit(spec: SpecFunc, types: MutableList[Type_specifier]) = { false }
}

/**
  * Vistor class to replace EnumName instances with EnumVar.
  */
class CCAstEnumNameToEnumVarVistor extends CCAstCopyWithLocation[Unit] {
  def apply(specifiers: ListDeclaration_specifier): ListDeclaration_specifier = {
    val copy = new ListDeclaration_specifier
    copy.addAll(specifiers.asScala.map(s => s.accept(this, ())).asJava)
    copy
  }

  /* Enum_specifier */
  override def visit(enum: EnumName, arg: Unit): Enum_specifier = {
    copyLocationInformation(enum, new EnumVar(enum.cident_))
  }
}
