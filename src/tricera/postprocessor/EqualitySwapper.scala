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
import IExpression.Predicate

import tricera.{
  ConstantAsProgVarProxy, HeapInfo, FunctionInvariants,
  PostCondition, PreCondition, ProgVarProxy, Invariant, Solution}
import tricera.concurrency.ccreader.CCExceptions.NeedsHeapModelException

object ToVariableForm extends ResultProcessor {

  override def applyTo(solution: Solution) = solution match {
    case Solution(functionInvariants) =>
      Solution(functionInvariants.map(applyTo(_)))
  }

  private def applyTo(funcInvs: FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      preCondition @ PreCondition(preInv),
      postCondition @ PostCondition(postInv),
      loopInvariants) =>
      val preCondValSet = ValSetReader.deBrujin(preInv.expression)
      val postCondValSet = ValSet.merge(
          ValSetReader.deBrujin(preInv.expression),
          ValSetReader.deBrujin(postInv.expression))
      val newInvs = FunctionInvariants(
        id,
        PreCondition(toVariableForm(preInv, preCondValSet, preCondition.isCurrentHeap)),
        PostCondition(toVariableForm(postInv, postCondValSet, postCondition.isCurrentHeap)),
        loopInvariants)
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  def toVariableForm(
    invariant: Invariant,
    valueSet: ValSet,
    isCurrentHeap: ProgVarProxy => Boolean)
    : Invariant = invariant match {
      case Invariant(form, maybeHeapInfo, maybeSourceInfo) => 
        Invariant(
          EqualitySwapper.deBrujin(
            form,
            valueSet.toVariableFormMap,
            isCurrentHeap).asInstanceOf[IFormula],
          maybeHeapInfo,
          maybeSourceInfo)
  }
}


object ToExplicitForm {
  def deBrujin(expr: IExpression, valueSet: ValSet, isCurrentHeap: ProgVarProxy => Boolean) = {
    EqualitySwapper.deBrujin(expr, valueSet.toExplicitFormMap, isCurrentHeap)
  } 

  def invariant(expr: IExpression, valueSet: ValSet, isCurrentHeap: ProgVarProxy => Boolean) = {
    EqualitySwapper.invariant(expr, valueSet.toExplicitFormMap, isCurrentHeap)
  } 
}

object EqualitySwapper {
  def deBrujin(expr: IExpression, swapMap: Map[IExpression, ITerm], isCurrentHeap: ProgVarProxy => Boolean) = {
    (new EqualitySwapper(swapMap, isCurrentHeap))(expr)
  }

  def invariant(expr: IExpression, swapMap: Map[IExpression, ITerm], isCurrentHeap: ProgVarProxy => Boolean) = {
    (new InvariantEqualitySwapper(swapMap, isCurrentHeap))(expr)
  }
}

class EqualitySwapper(swapMap: Map[IExpression, ITerm], isCurrentHeap: ProgVarProxy => Boolean)
    extends CollectingVisitor[Int, IExpression] 
    with ExpressionUtils {

  // swaps every expression except equalities but including the @h expression
  def apply(contractCondition: IExpression): IExpression = {
    def rewriter(expr: IExpression): IExpression = {
      visit(expr, 0)
    }
    iterateUntilFixedPoint(contractCondition, rewriter)
  }

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case IEquation(ConstantAsProgVarProxy(v), term) if !isCurrentHeap(v) =>
      ShortCutResult(t)
    case IEquation(term, ConstantAsProgVarProxy(v)) if !isCurrentHeap(v) =>
      ShortCutResult(t)
    case IIntFormula(IIntRelation.EqZero, term) =>
      ShortCutResult(t)
    case vb: IVariableBinder =>
      UniSubArgs(quantifierDepth + 1)
    case _ =>
      KeepArg
  }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[IExpression]
  ): IExpression = t match {
    case ConstantAsProgVarProxy(h) if isCurrentHeap(h) =>
      t update subres 
    case term: ITerm =>
      swapMap.get(term) match {
        case Some(variable) => variable
        case None => t update subres
      }
    case default => t update subres
  }
}

class InvariantEqualitySwapper(swapMap: Map[IExpression, ITerm], isCurrentHeap: ProgVarProxy => Boolean) 
  extends EqualitySwapper(swapMap, isCurrentHeap) {

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case IEquation(ConstantAsProgVarProxy(v), term) if !isCurrentHeap(v) =>
      ShortCutResult(t)
    case IEquation(term, ConstantAsProgVarProxy(v)) if !isCurrentHeap(v) =>
      ShortCutResult(t)
    case IIntFormula(IIntRelation.EqZero, term) =>
      ShortCutResult(t)
    case _ =>
      KeepArg
  }
}
