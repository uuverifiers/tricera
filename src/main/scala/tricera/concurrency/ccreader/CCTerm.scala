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
import tricera.params.TriCeraParameters

case class CCTerm(t               : ITerm,
                  typ             : CCType,
                  srcInfo         : Option[SourceInfo],
                  originalFormula : Option[IFormula]) {
  def toTerm : ITerm = t
  def toFormula : IFormula = originalFormula getOrElse {
    t match {
      case IIntLit(value) => !value.isZero
      case t if typ.isInstanceOf[CCHeapPointer] && TriCeraParameters.get.invEncoding.isEmpty =>
        !IExpression.Eq(t, typ.asInstanceOf[CCHeapPointer].heap.nullAddr())
      case t if typ == CCBool => t === ap.theories.ADT.BoolADT.True
      case t => !IExpression.eqZero(t)
    }
  }
  def occurringConstants: Seq[IExpression.ConstantTerm] =
    SymbolCollector constantsSorted t
  def convertToType(newType: CCType): CCTerm = {
    val isInvEncoding = TriCeraParameters.get.invEncoding.nonEmpty
    (typ, newType) match {
      case (oldType, newType) if (oldType == newType) =>
        this
      case (_: CCArithType, newType: CCArithType) =>
        newType cast this
      case (_: CCArithType, newType: CCHeapPointer) if isInvEncoding =>
        newType cast this
      case (_: CCArithType, CCDuration) => {
        if (!CCReader.useTime)
          throw NeedsTimeException
        CCTerm.fromTerm(CCReader.GTU.term * toTerm, CCDuration, srcInfo)
      }
      // newType is actually heap pointer
      //case (oldType : CCHeapPointer, newType : CCStackPointer) =>
      //  newType.typ cast t
      case (_, CCVoid) => this //
      // todo: do not do anything for casts to void?
      case (oldType: CCArithType, newType: CCHeapPointer) =>
        toTerm match {
          case lit: IIntLit if lit.value.intValue == 0 && TriCeraParameters.get.invEncoding.nonEmpty =>
            CCTerm.fromTerm(IIntLit(0), newType, srcInfo)
          case lit: IIntLit if lit.value.intValue == 0 =>
            CCTerm.fromTerm(newType.heap.nullAddr(), newType, srcInfo) //newType cast t
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

object CCTerm {
  def fromTerm(t : ITerm, typ : CCType, srcInfo : Option[SourceInfo]) : CCTerm =
    CCTerm(t, typ, srcInfo, None)

  def fromFormula(f: IFormula, typ: CCType, srcInfo: Option[SourceInfo]): CCTerm = {
    val fAsTerm : ITerm = f match {
      case IBoolLit(true)  => 1
      case IBoolLit(false) => 0
      case formula         => IExpression.ite(formula, 1, 0)
    }
    CCTerm(fAsTerm, typ, srcInfo, Some(f))
  }

  def unifyTypes(a: CCTerm, b: CCTerm): (CCTerm, CCTerm) = {
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
