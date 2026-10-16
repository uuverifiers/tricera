/**
 * Copyright (c) 2023-2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
import tricera.Util.{SourceInfo, getLineStringShort}
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
    (t, typ) match {
      case (t, ptrType : CCPointer) =>
        !IExpression.Eq(t, ptrType.nullPointer)
      case (IIntLit(value), _) => !value.isZero
      case (t, _) => !IExpression.eqZero(t)
    }
  }
  def occurringConstants: Seq[IExpression.ConstantTerm] =
    SymbolCollector constantsSorted t
  def convertToType(newType           : CCType,
                    conversionSrcInfo : Option[SourceInfo] = srcInfo): CCTerm = {
    (typ, newType) match {
      case (oldType, newType) if (oldType == newType) =>
        this
      case (_: CCArithType, newType: CCArithType) =>
        newType cast this
      case (_ : CCPointer, CCBool) =>
        CCBool cast this
      case (_: CCArithType, CCDuration) => {
        if (!CCReader.useTime)
          throw NeedsTimeException
        toTerm match {
          case IIntLit(value) =>
            CCTerm.fromTerm(CCReader.GTU.term * value, CCDuration, srcInfo)
          case _ =>
            throw new UnsupportedCFragmentException(
              getLineStringShort(conversionSrcInfo) +
              " Only integer literals are supported as clock or duration" +
              " values.")
        }
      }
      case (_: CCArithType | CCDuration, CCClock) =>
        val elapsed = convertToType(CCDuration, conversionSrcInfo).toTerm
        CCTerm.fromTerm(CCReader.GT.term - elapsed, CCClock, srcInfo)
      case (_: CCArithType, CCMathInt) =>
        CCTerm.fromTerm(toTerm, CCMathInt, srcInfo)
      case (CCMathInt, _: CCArithType) =>
        newType cast this
      case (_, CCVoid) => this
      case (_: CCArithType, newType: CCPointer) if isNullPointerConstant =>
        CCTerm.fromTerm(newType.nullPointer, newType, srcInfo)
      case (_: CCArithType, _: CCPointer) |
           (_: CCPointer, _: CCArithType) =>
        throw new UnsupportedCastException(
          getLineStringShort(conversionSrcInfo) +
          " Conversions between pointer and arithmetic types are not supported.")
      case (oldType: CCHeapPointer, newType: CCHeapPointer) =>
        newType cast this
      case (_ : CCStackPointer | _ : CCHeapArrayPointer | _ : CCArray,
            _ : CCHeapPointer) |
           (_ : CCHeapArrayPointer, _ : CCHeapArrayPointer) |
           (_ : CCArray, _ : CCArray) =>
        if (!CCTerm.isCompatiblePointerConversion(typ, newType))
          throw new UnsupportedCastException(
            getLineStringShort(conversionSrcInfo) +
            " incompatible pointer types: cannot convert " + typ.shortName +
            " to " + newType.shortName)
        this
      case (_ : CCNonArrayPointer | _ : CCArray, _ : CCHeapArrayPointer) =>
        throw new UnsupportedCFragmentException(
          getLineStringShort(conversionSrcInfo) + " Converting " +
          typ.shortName + " to an array pointer is not supported.")
      case (_ : CCStruct | _ : CCStructField, _ : CCStruct | _ : CCStructField)
          if CCTerm.underlyingType(typ) == CCTerm.underlyingType(newType) =>
        this
      case _ =>
        throw new UnsupportedCastException(
          "do not know how to convert " + typ + " to " + newType +
          " for term: " + toTerm + " (srcInfo: " + srcInfo + ")")
    }
  }

  private def isNullPointerConstant : Boolean = toTerm match {
    case IIntLit(value) => value.isZero
    case _              => false
  }

  def applyIntegerPromotion : CCTerm = typ match {
    case t : CCArithType if t.isNarrowerThanInt => convertToType(CCInt)
    case _ => this
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

  private def pointeeOrElementType(typ : CCType) : Option[CCType] = typ match {
    case p : CCStackPointer     => Some(p.typ)
    case p : CCHeapPointer      => Some(p.typ)
    case a : CCHeapArrayPointer => Some(a.elementType)
    case a : CCArray            => Some(a.elementType)
    case _                      => None
  }

  private def underlyingType(typ : CCType) : CCType = typ match {
    case f : CCStructField => f.structs(f.structName)
    case _                 => typ
  }

  private def isSameCType(a : CCType, b : CCType) : Boolean =
    (pointeeOrElementType(a), pointeeOrElementType(b)) match {
      case (Some(pa), Some(pb)) => isSameCType(pa, pb)
      case _ => (underlyingType(a), underlyingType(b)) match {
        case (e : CCIntEnum, t) => e == t || e.underlying == t
        case (t, e : CCIntEnum) => e.underlying == t
        case (ua, ub)           => ua == ub
      }
    }

  private def isCompatiblePointerConversion(from : CCType, to : CCType) : Boolean =
    pointeeOrElementType(from).contains(CCVoid) ||
    pointeeOrElementType(to).contains(CCVoid) ||
    isSameCType(from, to)

  private def enumUnificationType(e : CCIntEnum) : CCArithType =
    if (TriCeraParameters.get.arithMode == CCReader.ArithmeticMode.Mathematical)
      CCInt
    else e.underlying

  def unifyTypes(a: CCTerm, b: CCTerm): (CCTerm, CCTerm) = {
    (a.typ, b.typ) match {
      case (e : CCIntEnum, _) =>
        unifyTypes(a.convertToType(enumUnificationType(e)), b)
      case (_, e : CCIntEnum) =>
        unifyTypes(a, b.convertToType(enumUnificationType(e)))
      case (aType : CCArithType, _) if aType.isNarrowerThanInt =>
        unifyTypes(a.applyIntegerPromotion, b)
      case (_, bType : CCArithType) if bType.isNarrowerThanInt =>
        unifyTypes(a, b.applyIntegerPromotion)
      case _ if a.typ == b.typ =>
        (a, b)

      case (aType: CCArithType, bType: CCArithType) =>
        val commonType = CCArithType.commonType(aType, bType)
        (a convertToType commonType, b convertToType commonType)

      case (_: CCArithType, CCDuration) =>
        (a convertToType CCDuration, b)
      case (CCDuration, _: CCArithType) =>
        (a, b convertToType CCDuration)

      case (CCMathInt, _: CCArithType) =>
        (a, b convertToType CCMathInt)
      case (_: CCArithType, CCMathInt) =>
        (a convertToType CCMathInt, b)

      case (_: CCHeapArrayPointer, _ : CCArithType) =>
        (a, b) // pointer arithmetic, do not unify
      case (_ : CCArithType, _: CCHeapArrayPointer) =>
        (a, b)

      case (_: CCHeapPointer, _: CCHeapPointer) =>
        (a, b) // do not unify heap pointer types

      case _ =>
        throw new TranslationException(
          "incompatible types: " +
            a.typ + " vs " + b.typ)
    }
  }

  /** The type of `c ? thenVal : elseVal`, to which both operands are
   *  converted. */
  def conditionalResultType(thenVal : CCTerm,
                            elseVal : CCTerm,
                            srcInfo : Option[SourceInfo]) : CCType = {
    def unsupported(operands : String) =
      throw new UnsupportedCFragmentException(
        getLineStringShort(srcInfo) + " Conditional expressions whose " +
        "operands are " + operands + " are not supported.")
    // an integer operand next to a pointer has to be null, and only heap and
    // array pointers can be null, since the target of a stack pointer is fixed
    // in its type
    def isNullable(typ : CCType) =
      typ.isInstanceOf[CCHeapPointer] || typ.isInstanceOf[CCHeapArrayPointer]
    (thenVal.typ, elseVal.typ) match {
      case (_ : CCArithType | CCMathInt, _ : CCArithType | CCMathInt) =>
        unifyTypes(thenVal, elseVal)._1.typ
      case (thenType, elseType) if thenType == elseType =>
        thenType
      case (thenType, _ : CCArithType) if isNullable(thenType) =>
        thenType
      case (_ : CCArithType, elseType) if isNullable(elseType) =>
        elseType
      case (thenType : CCHeapPointer, elseType : CCHeapPointer)
          if isCompatiblePointerConversion(thenType, elseType) =>
        if (elseType.typ == CCVoid) elseType else thenType
      case (thenType : CCHeapArrayPointer, elseType : CCHeapArrayPointer)
          if isCompatiblePointerConversion(thenType, elseType) =>
        thenType.copy(
          arrayLocation =
            if (thenType.arrayLocation == elseType.arrayLocation)
              thenType.arrayLocation
            else ArrayLocation.Unknown,
          declaredSize =
            if (thenType.declaredSize == elseType.declaredSize)
              thenType.declaredSize
            else None)
      case (thenType : CCStackPointer, elseType : CCStackPointer)
          if thenType.targetInd != elseType.targetInd ||
             thenType.fieldAddress != elseType.fieldAddress =>
        unsupported("stack pointers to different objects")
      case (thenType, elseType)
          if thenType.isPointerType && elseType.isPointerType =>
        if (isCompatiblePointerConversion(thenType, elseType))
          unsupported("pointers of different kinds")
        else
          unsupported("pointers to incompatible types")
      case (thenType, elseType) =>
        unsupported("of types " + thenType.shortName + " and " +
                    elseType.shortName)
    }
  }
}

class InitializerStack {
  private val values = new scala.collection.mutable.Stack[CCTerm]
  def push(value : CCTerm) : Unit = values.push(value)
  def pop() : CCTerm = values.pop()
  def isEmpty  : Boolean = values.isEmpty
  def nonEmpty : Boolean = values.nonEmpty
  def nextHasSort(sort : Sort) : Boolean =
    values.nonEmpty && Sort.sortOf(values.top.toTerm) == sort
}
