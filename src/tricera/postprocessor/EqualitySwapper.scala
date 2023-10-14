/**
 * Copyright (c) 2011-2019 Oskar Soederberg. All rights reserved.
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
import tricera.concurrency.CCReader.FunctionContext
import tricera.postprocessor.ContractConditionType._

object ToVariableForm extends ContractProcessor {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    val valueSet = cci.contractConditionType match {
      case Precondition =>
        ValSetReader.deBrujin(cci.precondition)
      case Postcondition =>
        ValSet.merge(
          ValSetReader.deBrujin(cci.precondition),
          ValSetReader.deBrujin(cci.postcondition)
        )
    }
    EqualitySwapper.deBrujin(cci.contractCondition, valueSet.toVariableFormMap, cci)
  }
}

object ToExplicitForm {
  def deBrujin(expr: IExpression, valueSet: ValSet, cci: ContractConditionInfo) = {
    EqualitySwapper.deBrujin(expr, valueSet.toExplicitFormMap, cci)
  } 

  def invariant(expr: IExpression, valueSet: ValSet, cci: ContractConditionInfo) = {
    EqualitySwapper.invariant(expr, valueSet.toExplicitFormMap, cci)
  } 
}

object EqualitySwapper {
  def deBrujin(expr: IExpression, swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo) = {
    (new EqualitySwapper(swapMap, cci))(expr)
  }

  def invariant(expr: IExpression, swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo) = {
    (new InvariantEqualitySwapper(swapMap, cci))(expr)
  }
}

class EqualitySwapper(swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo)
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
    case IEquation(v: ISortedVariable, term) if !cci.isCurrentHeap(v, quantifierDepth) =>
      ShortCutResult(t)
    case IEquation(term, v: ISortedVariable) if !cci.isCurrentHeap(v, quantifierDepth) =>
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
    case h: ISortedVariable if cci.isCurrentHeap(h, quantifierDepth) =>
      t update subres 
    case term: ITerm =>
      val res = t update subres
      val shiftedTerm =
        VariableShiftVisitor(term, quantifierDepth, -quantifierDepth)
      swapMap.get(shiftedTerm) match {
        case Some(variable) =>
          val newVariable =
            VariableShiftVisitor(variable, 0, quantifierDepth)
          newVariable
        case None =>
          res
      }
    case default => t update subres
  }
}

class InvariantEqualitySwapper(swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo) extends EqualitySwapper(swapMap, cci) {

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case IEquation(v: ISortedVariable, term) if !cci.isCurrentHeap(v, quantifierDepth) =>
      ShortCutResult(t)
    case IEquation(term, v: ISortedVariable) if !cci.isCurrentHeap(v, quantifierDepth) =>
      ShortCutResult(t)
    case IIntFormula(IIntRelation.EqZero, term) =>
      ShortCutResult(t)
    case _ =>
      KeepArg
  }
}
