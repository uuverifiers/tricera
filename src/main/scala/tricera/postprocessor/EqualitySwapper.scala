/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025 Zafer Esen. All rights reserved.
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

 /* EqualitySwapper.scala
 * 
 * Defines objects and classes for converting expressions to equivalent 
 * representations. The ToVariableForm processor is defined here.
 *
 * See ToVariableForm in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 */

package tricera.postprocessor

import ap.parser._
import IExpression.Eq
import tricera._

object ToVariableForm extends ResultProcessor {

  override def applyTo(solution: Solution) = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(applyTo), loopInvariants)
  }

  private def applyTo(funcInvs: FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      PreCondition(preInv),
      PostCondition(postInv),
      loopInvariants) =>
      val preCondValSet = ValSetReader(preInv.expression)
      val postCondValSet = ValSet.union(preCondValSet,
                                        ValSetReader(postInv.expression))
      val newInvs = FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(toVariableForm(preInv, preCondValSet)),
        PostCondition(toVariableForm(postInv, postCondValSet)),
        loopInvariants)
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  private def toVariableForm(invariant : Invariant,
                     valueSet : ValSet) : Invariant = invariant match {
    case Invariant(form, maybeHeapInfo, maybeSourceInfo) =>
      Invariant(
        EqualitySwapper(
          form,
          valueSet.toCanonicalFormMap).asInstanceOf[IFormula],
        maybeHeapInfo,
        maybeSourceInfo)
  }
}

object ToExplicitForm {
  def apply(expr : IExpression, valueSet : ValSet) =
    EqualitySwapper(expr, valueSet.toCanonicalFormMap)
}

object EqualitySwapper {
  def apply(expr : IExpression, swapMap : Map[IExpression, ITerm]) =
    (new EqualitySwapper(swapMap))(expr)
}

class EqualitySwapper(swapMap : Map[IExpression, ITerm])
    extends CollectingVisitor[Int, IExpression] 
    with ExpressionUtils {
  def apply(contractCondition : IExpression) : IExpression = {
    def rewriter(expr : IExpression) : IExpression = {
      visit(expr, 0)
    }
    iterateUntilFixedPoint(contractCondition, rewriter)
  }

  override def preVisit(t               : IExpression,
                        quantifierDepth : Int) : PreVisitResult = t match {
    // Do not swap if the result will be something like x = x
    case Eq(left, right) =>
      val rewrittenRight = swapMap.getOrElse(right, right)
      if (left == rewrittenRight)
        return ShortCutResult(t)
      val rewrittenLeft = swapMap.getOrElse(left, left)
      if (rewrittenLeft == right || rewrittenLeft == rewrittenRight)
        return ShortCutResult(t)
      KeepArg
    case IIntFormula(IIntRelation.EqZero, _) => ShortCutResult(t)
    case _ : IVariableBinder => UniSubArgs(quantifierDepth + 1)
    case _                   => KeepArg
  }

  override def postVisit(t               : IExpression,
                         quantifierDepth : Int,
                         subres          : Seq[IExpression]) : IExpression = {
    val updated = t update subres
    (updated, swapMap.getOrElse(updated, updated)) match {
      case (ConstantAsProgVarProxy(upd), ConstantAsProgVarProxy(swp))
        if upd.isPostExec && swp.isPreExec =>
        // Keep using the post var, this can only happen in a postconditon,
        // Reasoning is that we (probably) do not want to replace a post-var\
        // with a pre-var.
        upd
      case _                               => updated
    }
  }
}
