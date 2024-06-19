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

/* ClauseRemover.scala
 *
 * See ClauseRemover in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 * 
 * In this contract processor, clauses that are not expressible in ACSL
 * are removed.
 */

package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ContractConditionType._

object ClauseRemover extends ContractProcessor {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IFormula = {
    apply(cci.contractCondition, cci).asInstanceOf[IFormula]
  }

  // TODO: Use IFormula instead of IExpression?
  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    val noTOHExpr = CleanupVisitor(TheoryOfHeapRemoverVisitor(expr, cci))
    val noTOHOrExplPtrExpr = CleanupVisitor(ExplicitPointerRemover(noTOHExpr, cci))
    val noTrivialEqExpr = CleanupVisitor(TrivialEqualityRemover(noTOHOrExplPtrExpr, cci))
    val newContractCondition = CleanupVisitor(HeapEqualityRemover(noTrivialEqExpr, cci))
    newContractCondition
  }
}

object TheoryOfHeapRemoverVisitor {
  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    (new TheoryOfHeapRemoverVisitor(cci)).visit(expr, 0)
  }
}

class TheoryOfHeapRemoverVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, IExpression] {

  override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult =
    t match {
      case default =>
        KeepArg
    }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[IExpression]
  ): IExpression = t match {
    case IBinFormula(IBinJunctor.And, _, _) =>
      val f1 = subres(0)
      val f2 = subres(1)
      (ContainsTOHVisitor(f1, cci), ContainsTOHVisitor(f2, cci)) match {
        case (false, false) =>
          t update subres
        case (true, false) =>
          f2
        case (false, true) =>
          f1
        case (true, true) =>
          IBoolLit(true)
      }
    case q @ ISortedQuantified(_, _, formula) =>
      q update subres
    case default => t update subres
  }
}

object ContainsTOHVisitor {
  def apply(expr: IExpression, cci: ContractConditionInfo): Boolean = {
    (new ContainsTOHVisitor(cci))(expr)
  }
}

class ContainsTOHVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Unit, Boolean] {

  def apply(expr: IExpression): Boolean = {
    visit(expr, ())
  }

  override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
    case TheoryOfHeapFunApp(_, _) =>
      ShortCutResult(true)
    case IFunApp(fun, args) if (cci.isGetter(fun) || cci.isWrapper(fun)) =>
      ShortCutResult(true)
    case _ =>
      KeepArg
  }

  override def postVisit(
      t: IExpression,
      arg: Unit,
      subres: Seq[Boolean]
  ): Boolean =
    if (subres.isEmpty) false else subres.reduce(_ || _)
}

object ExplicitPointerRemover extends ContractProcessor {
  def processContractCondition(cci: ContractConditionInfo): IFormula = {
    (new ExplicitPointerRemoverVisitor(cci)).visit(cci.contractCondition, 0).asInstanceOf[IFormula]
  }

  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    val newExpr = (new ExplicitPointerRemoverVisitor(cci)).visit(expr, 0)
    CleanupVisitor(newExpr)
  }
}

class ExplicitPointerRemoverVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, IExpression] {

  override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult =
    t match {
      case vb: IVariableBinder =>
        UniSubArgs(quantifierDepth + 1)
      case _ =>
        KeepArg
    }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[IExpression]
  ): IExpression = {
    t update subres match {
    case f: IFormula if ContainsExplicitPointerVisitor(f, quantifierDepth, cci) =>
      IBoolLit(true)
    case _ =>
      t update subres
    }
  }
}

object ContainsExplicitPointerVisitor {
  def apply(expr: IExpression, quantifierDepth: Int, cci: ContractConditionInfo): Boolean = {
    (new ContainsExplicitPointerVisitor(cci))(expr, quantifierDepth)
  }
}

class ContainsExplicitPointerVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, Boolean] {
  def apply(expr: IExpression, quantifierDepth: Int): Boolean = {
    visit(expr, quantifierDepth)
  }

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = {
    t match {
      case vb: IVariableBinder =>
        UniSubArgs(quantifierDepth + 1)

      case IEquation(v1: ISortedVariable, v2: ISortedVariable)
          if cci.isPointer(v1, quantifierDepth) && cci.isPointer(
            v2,
            quantifierDepth
          ) =>
        ShortCutResult(false)
      case TheoryOfHeapFunApp(_, _) =>
        ShortCutResult(false)
      case IFunApp(fun, _) if cci.isACSLFunction(fun) =>
        ShortCutResult(false)
      case IAtom(pred, _) if cci.isACSLPredicate(pred) =>
        ShortCutResult(false)
      case IBinFormula(IBinJunctor.And, _, _) =>
        ShortCutResult(false)
      case _ =>
        KeepArg
    }
  }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[Boolean]
  ): Boolean = t match {
    case v: ISortedVariable if cci.isPointer(v, quantifierDepth) =>
      true
    case _ =>
      if (subres.isEmpty) false else subres.reduce(_ || _)
  }
}

object TrivialEqualityRemover {
  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    (new TrivialEqualityRemover(cci)).visit(expr, ())
  }
}

class TrivialEqualityRemover(cci: ContractConditionInfo)
    extends CollectingVisitor[Unit, IExpression] {

  override def postVisit(
      t: IExpression,
      arg: Unit,
      subres: Seq[IExpression]
  ): IExpression = t match {
    case IEquation(left, right) if left == right =>
      IBoolLit(true)
    case _ =>
      t update subres
  }
}

object HeapEqualityRemover {
  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    (new HeapEqualityRemover(cci)).visit(expr, 0)
  }
}

class HeapEqualityRemover(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, IExpression] {

  override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult =
    t match {
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
    case IEquation(left: ISortedVariable, _) if cci.isCurrentHeap(left, quantifierDepth) =>
      IBoolLit(true)
    case IEquation(_, right: ISortedVariable) if cci.isCurrentHeap(right, quantifierDepth) =>
      IBoolLit(true)
    case _ =>
      t update subres
  }
}
