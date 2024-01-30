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

import ap.parser.{IExpression, IFormula, ITerm}
import ap.theories.ModuloArithmetic
import tricera.concurrency.CCReader._
import tricera.concurrency.ccreader.CCExceptions.TranslationException
import IExpression._
import tricera.Util.getLineString

object CCBinaryExpressions {
  object BinaryOperators {
    abstract sealed class BinaryOperation(_lhs: CCExpr, _rhs: CCExpr) {
      def isFormula = this match {
        case _: Equality | _: Disequality | _: Less | _: LessEqual |
            _: Greater | _: GreaterEqual =>
          true
        case _ => false
      }
      val (lhs, rhs) =
        if (isFormula) (_lhs, _rhs) else CCExpr.unifyTypes(_lhs, _rhs)
      // to note: pointer arithmetic types (arrayptr, arith) are not unified.
      // these should be handled in relevant cases supporting pointer arithmetic,
      // e.g., addition

      protected def getFloatRes: IExpression
      protected def getIntRes:   IExpression

      def expr: CCExpr = {
        try {(lhs.typ, rhs.typ) match {
          case (CCFloat, _) => toCCExpr(getFloatRes)
          case (_, CCFloat) => toCCExpr(getFloatRes)
          case _            => toCCExpr(getIntRes)
        }} catch {
          case e : IllegalArgumentException =>
            throw new TranslationException(
              getLineString(lhs.srcInfo) +
              s"Could not apply binary operator: $this\n")
          case e => throw e
        }
      }

      private def toCCExpr(exp: IExpression): CCExpr = {
        exp match {
          case term: ITerm =>
            val resultType = lhs.typ
            CCTerm(resultType cast term, resultType, lhs.srcInfo)
          case f: IFormula =>
            CCFormula(f, CCInt, lhs.srcInfo)
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Bitwise binary functions
    // note: cast2unsigned is important because rhs might be IdealInt
    case class BitwiseOr(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes =
        ModuloArithmetic.bvor(lhs.typ cast2Unsigned lhs.toTerm,
                              lhs.typ cast2Unsigned rhs.toTerm)
      override def getFloatRes = ???
    }

    case class BitwiseAnd(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes =
        ModuloArithmetic.bvand(lhs.typ cast2Unsigned lhs.toTerm,
                               lhs.typ cast2Unsigned rhs.toTerm)
      override def getFloatRes = ???
    }

    case class BitwiseXor(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes =
        ModuloArithmetic.bvxor(lhs.typ cast2Unsigned lhs.toTerm,
                               lhs.typ cast2Unsigned rhs.toTerm)
      override def getFloatRes = ???
    }

    case class ShiftLeft(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes =
        ModuloArithmetic.bvshl(lhs.typ cast2Unsigned lhs.toTerm,
                               lhs.typ cast2Unsigned rhs.toTerm)
      override def getFloatRes = ???
    }

    case class ShiftRight(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes =
        ModuloArithmetic.bvashr(lhs.typ cast2Unsigned lhs.toTerm,
                                lhs.typ cast2Unsigned rhs.toTerm)
      override def getFloatRes = ???
    }

    ////////////////////////////////////////////////////////////////////////////
    // Binary predicates
    // && and || are encoded in CCReader
    case class Equality(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      val (lhsTerm, rhsTerm) = getActualOperandsForBinPred(lhs, rhs)

      override def getIntRes   = lhsTerm === rhsTerm
      override def getFloatRes = ???
    }

    case class Disequality(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      val (lhsTerm, rhsTerm) = getActualOperandsForBinPred(lhs, rhs)

      override def getIntRes   = lhsTerm =/= rhsTerm
      override def getFloatRes = ???
    }

    case class Less(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      val (lhsTerm, rhsTerm) = getActualOperandsForBinPred(lhs, rhs)

      override def getIntRes   = lhsTerm < rhsTerm
      override def getFloatRes = ???
    }

    case class Greater(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      val (lhsTerm, rhsTerm) = getActualOperandsForBinPred(lhs, rhs)

      override def getIntRes   = lhsTerm > rhsTerm
      override def getFloatRes = ???
    }

    case class LessEqual(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      val (lhsTerm, rhsTerm) = getActualOperandsForBinPred(lhs, rhs)

      override def getIntRes   = lhsTerm <= rhsTerm
      override def getFloatRes = ???
    }

    case class GreaterEqual(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      val (lhsTerm, rhsTerm) = getActualOperandsForBinPred(lhs, rhs)

      override def getIntRes   = lhsTerm >= rhsTerm
      override def getFloatRes = ???
    }

    ////////////////////////////////////////////////////////////////////////////
    // Binary functions
    case class Plus(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes = (lhs.typ, rhs.typ) match {
        case (arrTyp: CCHeapArrayPointer, _: CCArithType) =>
          import arrTyp.heap._
          addressRangeCtor(nth(lhs.toTerm, rhs.toTerm),
                           addrRangeSize(lhs.toTerm) - rhs.toTerm)
        case _ =>
          lhs.toTerm + rhs.toTerm
      }
      override def getFloatRes = ???
    }

    case class Minus(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes = {
        throwErrorIfPointerArithmetic(lhs, rhs)
        lhs.toTerm - rhs.toTerm
      }
      override def getFloatRes = ???
    }

    case class Times(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes = {
        throwErrorIfPointerArithmetic(lhs, rhs)
        ap.theories.nia.GroebnerMultiplication.mult(lhs.toTerm, rhs.toTerm)
      }
      override def getFloatRes = ???
    }

    case class Div(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes = {
        throwErrorIfPointerArithmetic(lhs, rhs)
        ap.theories.nia.GroebnerMultiplication.tDiv(lhs.toTerm, rhs.toTerm)
      }
      override def getFloatRes = ???
    }

    case class Mod(_lhs: CCExpr, _rhs: CCExpr)
        extends BinaryOperation(_lhs, _rhs) {
      override def getIntRes = {
        throwErrorIfPointerArithmetic(lhs, rhs)
        ap.theories.nia.GroebnerMultiplication.tMod(lhs.toTerm, rhs.toTerm)
      }
      override def getFloatRes = ???
    }

    private def throwErrorIfPointerArithmetic(lhs: CCExpr,
                                              rhs: CCExpr): Unit = {
      (lhs.typ, rhs.typ) match {
        case (_: CCHeapArrayPointer, _: CCArithType) =>
          throw new TranslationException(
            "Pointer arithmetic over arrays is only  supported with  addition.")
        case _ => // nothing
      }
    }

    private def getActualOperandsForBinPred(lhs: CCExpr,
                                            rhs: CCExpr): (ITerm, ITerm) = {
      (lhs.typ, rhs.typ) match {
        case (CCClock, _: CCArithType) =>
          (GT.term - lhs.toTerm, GTU.term * rhs.toTerm)
        case (_: CCArithType, CCClock) =>
          (GTU.term * lhs.toTerm, GT.term - rhs.toTerm)
        case (CCClock, CCClock) =>
          (-lhs.toTerm, -rhs.toTerm)
        case (CCDuration, _: CCArithType) =>
          (lhs.toTerm, GTU.term * rhs.toTerm)
        case (_: CCArithType, CCDuration) =>
          (GTU.term * lhs.toTerm, rhs.toTerm)
        case (CCDuration, CCDuration) =>
          (lhs.toTerm, rhs.toTerm)
        case (CCClock, CCDuration) =>
          (GT.term - lhs.toTerm, rhs.toTerm)
        case (CCDuration, CCClock) =>
          (lhs.toTerm, GT.term - rhs.toTerm)
        case _ =>
          (lhs.toTerm, rhs.toTerm)
      }
    }
  }
}
