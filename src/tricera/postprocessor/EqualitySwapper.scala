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
import tricera.concurrency.CCReader.FunctionContext
import tricera.postprocessor.ContractConditionType._
import tricera.{ResultUtils, IFuncParam}

object ToVariableForm extends ContractProcessor with ResultUtils {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IFormula = {
    val valueSet = cci.contractConditionType match {
      case Precondition =>
        ValSetReader.deBrujin(cci.precondition)
      case Postcondition =>
        ValSet.merge(
          ValSetReader.deBrujin(cci.precondition),
          ValSetReader.deBrujin(cci.postcondition)
        )
    }
    EqualitySwapper.deBrujin(cci.contractCondition, valueSet.toVariableFormMap).asInstanceOf[IFormula]
  }
}

object ToExplicitForm {
  def deBrujin(expr: IExpression, valueSet: ValSet) = {
    EqualitySwapper.deBrujin(expr, valueSet.toExplicitFormMap)
  } 

  def invariant(expr: IExpression, valueSet: ValSet) = {
    EqualitySwapper.invariant(expr, valueSet.toExplicitFormMap)
  } 
}

object EqualitySwapper {
  def deBrujin(expr: IExpression, swapMap: Map[IExpression, ITerm]) = {
    (new EqualitySwapper(swapMap))(expr)
  }

  def invariant(expr: IExpression, swapMap: Map[IExpression, ITerm]) = {
    (new InvariantEqualitySwapper(swapMap))(expr)
  }
}

class EqualitySwapper(swapMap: Map[IExpression, ITerm])
    extends CollectingVisitor[Int, IExpression] 
    with ExpressionUtils
    with ResultUtils {

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
    case IEquation(v: IFuncParam, term) if !isCurrentHeap(v) =>
      ShortCutResult(t)
    case IEquation(term, v: IFuncParam) if !isCurrentHeap(v) =>
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
    case h: IFuncParam if isCurrentHeap(h) =>
      t update subres 
    case term: ITerm =>
      swapMap.get(term) match {
        case Some(variable) => variable
        case None => t update subres
      }
    case default => t update subres
  }
}

class InvariantEqualitySwapper(swapMap: Map[IExpression, ITerm]) 
  extends EqualitySwapper(swapMap) with ResultUtils {

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case IEquation(v: IFuncParam, term) if !isCurrentHeap(v) =>
      ShortCutResult(t)
    case IEquation(term, v: IFuncParam) if !isCurrentHeap(v) =>
      ShortCutResult(t)
    case IIntFormula(IIntRelation.EqZero, term) =>
      ShortCutResult(t)
    case _ =>
      KeepArg
  }
}
