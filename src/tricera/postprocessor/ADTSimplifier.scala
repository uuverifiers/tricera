/**
 * Copyright (c) 2023 Oskar Soederberg. All rights reserved.
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

 /* ADTSimplifier.scala
 *
 * See ADTProcessor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 * 
 * In this step, struct expressions are reduced to a simpler form containing 
 * fewer subexpressions, which can be handled by the ACSLExpressionProcessor
 */

package tricera.postprocessor

import ap.parser._

import ap.theories.{ADT, Theory, TheoryRegistry}
import ap.types.{MonoSortedIFunction, SortedConstantTerm}

import tricera.{FunctionInvariants, Invariant, PostCondition, PreCondition, Solution}


object ADTSimplifier extends ResultProcessor {
  override def applyTo(solution: Solution): Solution = solution match {
    case Solution(functionInvariants) => 
      Solution(functionInvariants.map(applyTo))
  }

  private def applyTo(funcInvs: FunctionInvariants): FunctionInvariants = funcInvs match {
    case FunctionInvariants(id, PreCondition(preInv), PostCondition(postInv), loopInvariants) => 
      val newInvs = FunctionInvariants(
        id,
        PreCondition(simplify(preInv)),
        PostCondition(simplify(postInv)),
        loopInvariants)
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  private def simplify(invariant: Invariant): Invariant = invariant match {
    case Invariant(form, heapInfo, srcInfo) =>
      val simplifier = new ADTTermSimplifier()
      Invariant(simplifier(form).asInstanceOf[IFormula], heapInfo, srcInfo)
  }
}

private class ADTTermSimplifier extends CollectingVisitor[Unit, IExpression] {
  def apply(exp: IExpression): IExpression = {
    visit(exp, ())
  }

  override def postVisit(
      t: IExpression,
      none: Unit,
      subres: Seq[IExpression]
  ): IExpression = {
    object SelectorWrappingConstructor {
      /**
        * Extract constructor argument term corresponding to the
        * applied selector.
        *
        * @param funcApp 
        * @return The constructor argument term
        */
      def unapply(funcApp: IFunApp): Option[ITerm] = funcApp match {
        case IFunApp(
            outer: MonoSortedIFunction,
            Seq(IFunApp(inner: MonoSortedIFunction, args))) =>
          outer match {
            case ADT.Selector(adt, ctorIndex, argIndex) =>
              // 'outer' is a selector
              inner match {
                case ADT.Constructor(adt, innerCtorIndex) if (innerCtorIndex == ctorIndex) =>
                  // 'inner' is a constructor matching the outer selector
                  Some(args(argIndex))
                case _ => None
              }
            case _ => None
          }
        case _ => None
      }
    }

    t match {
      // S(x,y).a -> x
      case SelectorWrappingConstructor(value) => value
      case _ =>t update subres
    }
  }
}
