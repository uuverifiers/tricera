/**
 * Copyright (c) 2023 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package tricera.concurrency.ccreader

import ap.parser.{IBoolLit, IExpression, IFormula, IIntLit, ITerm, SymbolCollector}
import tricera.Util.SourceInfo
import CCExceptions._
import ap.parser.IExpression._
import tricera.concurrency.CCReader

abstract sealed class CCExpr(val typ: CCType, val srcInfo: Option[SourceInfo]) {
  def toTerm:             ITerm
  def toFormula:          IFormula
  def occurringConstants: Seq[IExpression.ConstantTerm]

  def convertToType(newType: CCType): CCExpr = {
    (typ, newType) match {
      case (oldType, newType) if (oldType == newType) =>
        this
      case (oldType: CCArithType, newType: CCArithType) =>
        newType cast this
      case (oldType: CCArithType, CCDuration) => {
        if (!CCReader.useTime)
          throw NeedsTimeException
        CCTerm(CCReader.GTU.term * toTerm, CCDuration, srcInfo)
      }
      // newType is actually heap pointer
      //case (oldType : CCHeapPointer, newType : CCStackPointer) =>
      //  newType.typ cast t
      case (_, CCVoid) => this //
      // todo: do not do anything for casts to void?
      case (oldType: CCArithType, newType: CCHeapPointer) =>
        toTerm match {
          case lit: IIntLit if lit.value.intValue == 0 =>
            CCTerm(newType.heap.nullAddr(), newType, srcInfo) //newType cast t
          case _ =>
            throw new UnsupportedCastException(
              "pointer arithmetic is not allowed, cannot convert " + this + " to" +
                " " + newType)
        }
      case (oldType : CCHeapPointer, newType : CCArithType) =>
        throw new UnsupportedCastException(
          "Cannot cast pointer type to arithmetic type.")
      case (oldType: CCHeapPointer, newType: CCHeapPointer) =>
        newType cast this
      case _ =>
        throw new UnsupportedCastException(
          "do not know how to convert " + typ + " to " + newType +
            " for term: " + toTerm + " (srcInfo: " + srcInfo + ")")
    }
  }
}

case class CCTerm(t: ITerm, _typ: CCType, _srcInfo: Option[SourceInfo])
    extends CCExpr(_typ, _srcInfo) {
  def toTerm: ITerm = t
  def toFormula: IFormula = t match {
    case IIntLit(value) => !value.isZero
    case t if _typ.isInstanceOf[CCHeapPointer] =>
      !IExpression.Eq(t,
                      _typ
                        .asInstanceOf[CCHeapPointer]
                        .heap
                        .nullAddr())
    case t if _typ == CCBool => t === ap.theories.ADT.BoolADT.True
    case t => !IExpression.eqZero(t)
  }
  def occurringConstants: Seq[IExpression.ConstantTerm] =
    SymbolCollector constantsSorted t
}

case class CCFormula(f: IFormula, _typ: CCType, _srcInfo: Option[SourceInfo])
    extends CCExpr(_typ, _srcInfo: Option[SourceInfo]) {
  def toTerm: ITerm = f match {
    case IBoolLit(true)  => 1
    case IBoolLit(false) => 0
    case f               => IExpression.ite(f, 1, 0)
  }
  def toFormula: IFormula = f
  def occurringConstants: Seq[IExpression.ConstantTerm] =
    SymbolCollector constantsSorted f
}

object CCExpr {
  def unifyTypes(a: CCExpr, b: CCExpr): (CCExpr, CCExpr) = {
    (a.typ, b.typ) match {
      case _ if a.typ == b.typ =>
        (a, b)

      case (aType: CCArithType, bType: CCArithType) =>
        if ((aType.UNSIGNED_RANGE > bType.UNSIGNED_RANGE) ||
            (aType.UNSIGNED_RANGE == bType.UNSIGNED_RANGE && aType.isUnsigned))
          (a, b convertToType aType)
        else
          (a convertToType bType, b)

      case (_: CCArithType, CCDuration) =>
        (a convertToType CCDuration, b)
      case (CCDuration, _: CCArithType) =>
        (a, b convertToType CCDuration)

      case (_: CCHeapArrayPointer, _ : CCArithType) =>
        (a, b) // pointer arithmetic, do not unify

      case (_: CCHeapPointer, _: CCHeapPointer) =>
        (a, b) // do not unify heap pointer types

      case _ =>
        throw new TranslationException(
          "incompatible types: " +
            a.typ + " vs " + b.typ)
    }
  }
}
