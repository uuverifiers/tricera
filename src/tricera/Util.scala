/**
 * Copyright (c) 2021-2022 Zafer Esen. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
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

package tricera
import ap.parser.{IExpression, IFunApp, ITerm}
import ap.theories.ExtArray
import ap.types.MonoSortedIFunction
import tricera.concurrency.CCReader.TranslationException
import tricera.concurrency.concurrent_c.Absyn._

import scala.collection.mutable

object Util {
  def warn(msg : String) : Unit =
    Console.err.println("Warning: " + msg)

  case class SourceInfo (line : Int, col : Int, offset : Int)

  // todo: is below really the only way to get line numbers?
  def getSourceInfo(exp: Exp): SourceInfo = exp match {
    case exp: Ecomma => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eassign => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Econdition => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Elor => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eland => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebitor => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebitexor => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebitand => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eeq => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eneq => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Elthen => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Egrthen => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ele => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ege => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eleft => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eright => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eplus => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eminus => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Etimes => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ediv => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Emod => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Etypeconv => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epreinc => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epredec => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epreop => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebytesexpr => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebytestype => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Earray => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Efunk => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Efunkpar => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eselect => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epoint => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epostinc => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epostdec => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Evar => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Econst => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Estring => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Enondet => SourceInfo(exp.line_num, exp.col_num, exp.offset)
  }

  def getLineString(exp: Exp): String = {
    val sourceInfo = getSourceInfo(exp)
    "At line " + sourceInfo.line + " (offset " + sourceInfo.offset + "): "
  }

  /**
   * Helper function to write to ADT fields. This code was taken almost verbatim
   * from the similar method in the ap.theories.Heap.
   * todo: move this to another class, maybe a new one for helper functions
   *   for IFormulas (or add to Princess)
   * @param lhs : the ADT field term to be written to. This should be an IFunApp,
   *            where the outermost function is a selector of the ADT, the
   *            innermost function is a heap read to the ADT on the heap, the
   *            innermost+1 function is the getter of the ADT, and any
   *            intermediate functions are other selectors
   *            e.g. select(a(s), i) or  (in C: s.a[i])
   * @param rhs : the new value for the field, e.g. 42
   * this would return a new term, such as: S(store(a, i, 42))
   * @return    : the new ADT term
   */
  def writeADT (lhs : IFunApp, rhs : ITerm,
                adtCtors : Seq[MonoSortedIFunction],
                adtSels : Seq[Seq[MonoSortedIFunction]]) : ITerm = {
    import IExpression.toFunApplier

    case class ADTFieldPath (ctor : MonoSortedIFunction,
                                     sels : Seq[MonoSortedIFunction],
                                     updatedSelInd : Int)
    def generateADTUpdateStack (termPointingToADTField : IFunApp)
    : (List[ADTFieldPath], ITerm) = {
      val ADTUpdateStack = new mutable.Stack[ADTFieldPath]

      def fillParentStack (fieldTerm : IFunApp) : ITerm = {
        val maybeArrayTheory = ExtArray.Select.unapply(fieldTerm.fun)
        assert(fieldTerm.args.size == 1 || maybeArrayTheory.nonEmpty)
        fieldTerm.args.head match {
          case nested : IFunApp if adtCtors.exists(c =>
            c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort) &&
            ExtArray.Select.unapply(nested.fun).isEmpty =>

            // here two possibilities:
            // one is that the last level resSort is a getter
            //   (e.g. getS that has the same resSort as a ctor)
            // second is that the last level is simply the ctor
            val ctorInd =
              if(adtCtors contains nested.fun) { // first case
                adtCtors indexOf nested.fun
              } else { // second case
                adtCtors.indexWhere(c =>
                  c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort)
              }

            val sels = adtSels(ctorInd)
            val thisSelInd =
              adtSels(ctorInd).indexWhere(s => s == fieldTerm.fun)
            ADTUpdateStack.push(
              ADTFieldPath(adtCtors(ctorInd), sels, thisSelInd))
            // then move on to nested parents
            fillParentStack(nested)
          case _ => fieldTerm
        }
      }
      val rootTerm = fillParentStack (termPointingToADTField)
      (ADTUpdateStack.toList, rootTerm)
    }


    def updateADT(adtStack : List[ADTFieldPath], parentTerm : ITerm,
                  newVal : ITerm) : ITerm = {
      adtStack match {
        case Nil => // last level
          newVal
        case parent :: tl => import IExpression.toFunApplier
          val newTerm = updateADT(tl, parentTerm, newVal)
          val args = for (i <- parent.sels.indices) yield {
            if (i == parent.updatedSelInd) newTerm
            else parent.sels(i)(parentTerm)
          }
          parent.ctor(args : _*)
      }
    }

    val (adtStack, rootTerm) = generateADTUpdateStack(lhs)
    val newTerm = updateADT(adtStack, rootTerm, rhs)
    rootTerm match {
      case IFunApp(f, args) =>
        f match {
          case ExtArray.Select(arr) => // Object select (select(a, i))
            arr.store(args(0), args(1), newTerm)
          case _ => throw new TranslationException("Could not determine write from " +
            "the lhs: " + lhs)
        }
      case _ => throw new TranslationException("Could not determine write from " +
        "the lhs: " + lhs)
    }
  }
}
