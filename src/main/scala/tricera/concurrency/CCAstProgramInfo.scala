/**
 * Copyright (c) 2026 Zafer Esen. All rights reserved.
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

import scala.jdk.CollectionConverters._

import tricera.acsl.ACSLTranslator
import tricera.concurrency.ccreader.{CCType, CCInt, CCUInt, StructInfo}

// Facts about the program: how each type is used and in which function
// (None = global).

// onHeap: the type needs to be on the heap
sealed abstract class HeapUsageKind(val onHeap : Boolean)
case object ValueUse     extends HeapUsageKind(false) // by value
case object HeapAlloc    extends HeapUsageKind(true)  // malloc/calloc target
case object ArrayElem    extends HeapUsageKind(true)  // heap-modeled array element
case object PointerField extends HeapUsageKind(true)  // pointee of a struct pointer field
case object ContractPtr  extends HeapUsageKind(true)  // inside an ACSL annotation

// Structs are known only by tag here: their CCType is built with the heap ADT
sealed abstract class UsedType
object UsedType {
  case class Scalar(typ  : CCType) extends UsedType {
    override def toString : String = typ.toString
  }
  case class Struct(name : String) extends UsedType {
    override def toString : String = "struct " + name
  }
}

case class TypeUsage(enclosingFunction : Option[String],
                     typ               : UsedType,
                     kind              : HeapUsageKind)

class ProgramInfo(val usages : Seq[TypeUsage]) {
  def types                       : Set[UsedType] = usages.map(_.typ).toSet
  def typesIn(fn : Option[String]): Set[UsedType] =
    usages.collect { case TypeUsage(`fn`, t, _) => t }.toSet
  def isHeapType(t : UsedType)    : Boolean       =
    usages.exists(u => u.typ == t && u.kind.onHeap)
  lazy val heapTypes              : Set[UsedType] =
    usages.collect { case u if u.kind.onHeap => u.typ }.toSet
  def heapTypesIn(fn : Option[String]) : Set[UsedType] =
    usages.collect { case TypeUsage(`fn`, t, k) if k.onHeap => t }.toSet
  def needsHeap                   : Boolean       = heapTypes.nonEmpty
}

/**
  * Builds ProgramInfo for the program. Currently records the uses that place a
  * value on the heap: allocations, array elements, struct pointer fields.
  */
class CCAstProgramInfoCollector(structInfos  : Seq[StructInfo],
                                resolveAlloc : Ebytestype => Option[UsedType],
                                resolveDecl  : ListDeclaration_specifier => Option[UsedType]) {

  def apply(prog : Program) : ProgramInfo =
    new ProgramInfo(prog.accept(new UsageVisitor, None) ++ pointerFieldUses)

  // run f with stdout/stderr muted
  private def quietly[A](f : => A) : A = {
    val (oldOut, oldErr) = (System.out, System.err)
    val sink = new java.io.PrintStream(new java.io.OutputStream {
      override def write(b : Int) : Unit = ()
    })
    System.setOut(sink); System.setErr(sink)
    try f finally { System.setOut(oldOut); System.setErr(oldErr) }
  }

  // A pointer struct field is a heap pointer, so its pointee is a heap type
  private def pointerFieldUses : Seq[TypeUsage] =
    for (struct <- structInfos;
         field  <- struct.fieldInfos if field.ptrDepth > 0) yield {
      val typ = field.typ match {
        case Right(t)  => UsedType.Scalar(t)
        case Left(ind) => UsedType.Struct(structInfos(ind).name)
      }
      TypeUsage(None, typ, PointerField)
    }

  // heap type uses in the AST: malloc/calloc and array declarations
  private class UsageVisitor extends FoldVisitor[Seq[TypeUsage], Option[String]] {
    private val getName  = new CCAstGetNameVistor
    private val acslRefs = new ACSLReferencedNamesVisitor

    override def leaf(arg : Option[String]) : Seq[TypeUsage] = Seq.empty
    override def combine(x : Seq[TypeUsage], y : Seq[TypeUsage],
                         arg : Option[String]) : Seq[TypeUsage] = x ++ y

    override def visit(f : Afunc, arg : Option[String]) : Seq[TypeUsage] = {
      val fn = try Some(f.accept(getName, ())) catch { case _ : Throwable => arg }
      f.function_def_.accept(this, fn)
    }

    override def visit(call : Efunkpar, arg : Option[String]) : Seq[TypeUsage] = {
      val allocated = calleeName(call.exp_) match {
        case Some("malloc") | Some("calloc") =>
          sizeofArg(call).flatMap(resolveAlloc)
            .map(t => TypeUsage(arg, t, HeapAlloc)).toSeq
        case _ => Seq.empty
      }
      allocated ++ super.visit(call, arg)
    }

    // an array declaration puts its element type on the heap
    override def visit(decl : Declarators, arg : Option[String]) : Seq[TypeUsage] = {
      val elem =
        if (decl.listinit_declarator_.asScala.exists(isArrayDeclarator))
          resolveDecl(decl.listdeclaration_specifier_)
            .map(t => TypeUsage(arg, t, ArrayElem)).toSeq
        else Seq.empty
      elem ++ super.visit(decl, arg)
    }

    // heap types from ACSL annotations
    // struct tags + int/uint
    // TODO: proper detection of scalar types
    override def visit(annot : Annot1, arg : Option[String]) : Seq[TypeUsage] = {
      val marker = tricera.Literals.annotationMarker.length
      val text   = annot.annotationstring_
      val body   =
        if (text.length >= 2 * marker) text.substring(marker, text.length - marker)
        else text
      val names =
        try quietly(ACSLTranslator.parseToAST("/*@" + body + "*/").accept(acslRefs, ()))
        catch { case _ : Throwable => Set.empty[String] }
      val structs = structInfos.map(_.name).filter(names)
        .map(n => TypeUsage(arg, UsedType.Struct(n), ContractPtr))
      val scalars = Seq[CCType](CCInt, CCUInt)
        .map(t => TypeUsage(arg, UsedType.Scalar(t), ContractPtr))
      structs ++ scalars ++ super.visit(annot, arg)
    }

    private def isArrayDeclarator(init : Init_declarator) : Boolean = {
      val direct = (init match {
        case d : OnlyDecl     => Some(d.declarator_)
        case d : InitDecl     => Some(d.declarator_)
        case d : HintInitDecl => Some(d.declarator_)
        case _                => None
      }).flatMap {
        case d : NoPointer    => Some(d.direct_declarator_)
        case d : BeginPointer => Some(d.direct_declarator_)
        case _                => None
      }
      direct.exists(d =>
        d.isInstanceOf[InitArray] || d.isInstanceOf[Incomplete] || d.isInstanceOf[MathArray])
    }

    private def calleeName(exp : Exp) : Option[String] = exp match {
      case e : Evar         => Some(e.cident_)
      case e : EvarWithType => Some(e.cident_)
      case _                => None
    }

    private def sizeofArg(call : Efunkpar) : Option[Ebytestype] =
      call.listexp_.asScala.toList match {
        case (e : Ebytestype) :: Nil => Some(e)
        case (e : Etimes) :: Nil => (e.exp_1, e.exp_2) match {
          case (b : Ebytestype, _) => Some(b)
          case (_, b : Ebytestype) => Some(b)
          case _                   => None
        }
        case a :: b :: Nil => (a, b) match {
          case (b2 : Ebytestype, _) => Some(b2)
          case (_, b2 : Ebytestype) => Some(b2)
          case _                    => None
        }
        case _ => None
      }
  }
}
