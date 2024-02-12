/**
 * Copyright (c) 2021-2022 Zafer Esen. All rights reserved.
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

package tricera.postprocessor

import ap.parser._
import ap.theories.ADT.ADTProxySort
import ap.theories.{ADT, TheoryRegistry}
import ap.types.{MonoSortedIFunction, SortedConstantTerm}

object ADTExploder extends SolutionProcessor {
  def apply(expr : IFormula) : IFormula =
    Rewriter.rewrite(expr, explodeADTs).asInstanceOf[IFormula]

  case class ADTTerm(t : ITerm, adtSort : ADTProxySort)
  object adtTermExploder extends CollectingVisitor[Object, IExpression] {
    def getADTTerm(t : IExpression) : Option[ADTTerm] = {
      t match {
        case f @ IFunApp(fun, _) if ADT.Constructor.unapply(fun).nonEmpty =>
          val sortedFun = fun.asInstanceOf[MonoSortedIFunction]
          val adtSort = sortedFun.resSort.asInstanceOf[ADT.ADTProxySort]
          Some(ADTTerm(f, adtSort))
        case c@IConstant(SortedConstantTerm(_, sort))
          if sort.isInstanceOf[ADTProxySort] =>
          Some(ADTTerm(c, sort.asInstanceOf[ADTProxySort]))
        case _ => None
      }
    }

    override def postVisit(t: IExpression, none : Object,
                           subres: Seq[IExpression]) : IExpression = {

      import IExpression._
      def explodeADTSelectors (originalEq : IEquation, ctorFun : IFunction,
                               lhsIsCtor : Boolean) = {
        val newEq = originalEq update subres
        val (newFunApp, selectorTerms, newRootTerm) =
          if (lhsIsCtor) {
            val Eq(newFunApp@IFunApp(_, selectorTerms), newRootTerm) = newEq
            (newFunApp, selectorTerms, newRootTerm)
          } else {
            val Eq(newRootTerm, newFunApp@IFunApp(_, selectorTerms)) = newEq
            (newFunApp, selectorTerms, newRootTerm)
          }
        val adtTerm = getADTTerm(newFunApp).get
        val adt = adtTerm.adtSort.adtTheory
        val ctorIndex = adt.constructors.indexOf(ctorFun)
        val selectors = adt.selectors(ctorIndex)
        (for ((fieldTerm, selectorInd) <- selectorTerms zipWithIndex)
          yield selectors(selectorInd)(newRootTerm) ===
            fieldTerm.asInstanceOf[ITerm]).reduce(_ &&& _)
      }

      t match {
        case e@Eq(funApp@IFunApp(fun, _), _) if getADTTerm(funApp).nonEmpty =>
          explodeADTSelectors(e.asInstanceOf[IEquation], fun, lhsIsCtor = true)
        case e@Eq(_, funApp@IFunApp(fun, _)) if getADTTerm(funApp).nonEmpty =>
          explodeADTSelectors(e.asInstanceOf[IEquation], fun, lhsIsCtor = false)
        case t@IFunApp(f,_) =>
          val newApp = t update subres
          (for (theory <- TheoryRegistry lookupSymbol f;
                res <- theory evalFun newApp) yield res) getOrElse newApp
        case _ =>
          t update subres
      }
    }
  }

  // converts "s = S(a, b)" to "f1(s) = a & f2(s) = b"
  private def explodeADTs(expr : IExpression) : IExpression =
    adtTermExploder.visit(expr, null)

}
