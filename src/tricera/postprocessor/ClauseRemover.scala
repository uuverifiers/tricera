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

import tricera.{
  ConstantAsProgVarProxy, FunctionInvariants, HeapInfo, Invariant,
  PostCondition, PreCondition, ProgVarProxy, Solution}

object ClauseRemover extends ResultProcessor {
  override def applyTo(solution: Solution): Solution = solution match {
    case Solution(functionInvariants) =>
      Solution(functionInvariants.map(applyTo(_)))
  }

  private def applyTo(funcInvs: FunctionInvariants): FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      preCond @ PreCondition(preInv),
      postCond @ PostCondition(postInv),
      loopInvariants) => 
      val newInvs = FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(applyTo(preInv, preCond.isCurrentHeap)),
        PostCondition(applyTo(postInv, postCond.isCurrentHeap)),
        loopInvariants)
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  private def applyTo(invariant: Invariant, isCurrentHeap: ProgVarProxy => Boolean)
    : Invariant = invariant match {
    case Invariant(expression, Some(heapInfo), sourceInfo) =>
      val noTOHExpr = CleanupVisitor(TheoryOfHeapRemoverVisitor(expression, heapInfo))
      val noTOHOrExplPtrExpr = CleanupVisitor(ExplicitPointerRemover(noTOHExpr))
      val noTrivialEqExpr = CleanupVisitor(TrivialEqualityRemover(noTOHOrExplPtrExpr))
      val newForm = CleanupVisitor(
        HeapEqualityRemover(noTrivialEqExpr, isCurrentHeap)).asInstanceOf[IFormula]
      Invariant(newForm, Some(heapInfo), sourceInfo)
    case Invariant(expression, None, sourceInfo) => 
      val newForm = CleanupVisitor(TrivialEqualityRemover(expression)).asInstanceOf[IFormula]
      Invariant(newForm, None, sourceInfo)
  }
}

object TheoryOfHeapRemoverVisitor {
  def apply(expr: IExpression, cci: HeapInfo): IExpression = {
    (new TheoryOfHeapRemoverVisitor(cci)).visit(expr, ())
  }

  class TheoryOfHeapRemoverVisitor(cci: HeapInfo)
    extends CollectingVisitor[Unit, IExpression] {

    override def postVisit(
        t: IExpression,
        dummy: Unit,
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
}


object ContainsTOHVisitor {
  def apply(expr: IExpression, cci: HeapInfo): Boolean = {
    (new ContainsTOHVisitor(cci))(expr)
  }

  class ContainsTOHVisitor(cci: HeapInfo)
      extends CollectingVisitor[Unit, Boolean] {
  
    def apply(expr: IExpression): Boolean = {
      visit(expr, ())
    }
  
    override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
      case TheoryOfHeapFunApp(_, _) =>
        ShortCutResult(true)
      case IFunApp(fun, args) if (cci.isObjSelector(fun) || cci.isObjCtor(fun)) =>
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
}


object ExplicitPointerRemover {
  def apply(expr: IExpression): IExpression = {
    val newExpr = (new ExplicitPointerRemoverVisitor).visit(expr, ())
    CleanupVisitor(newExpr)
  }

  class ExplicitPointerRemoverVisitor
      extends CollectingVisitor[Unit, IExpression] {
  
    override def postVisit(
        t: IExpression,
        dummy: Unit,
        subres: Seq[IExpression]
    ): IExpression = {
      t update subres match {
      case f: IFormula if ContainsExplicitPointerVisitor(f) =>
        IBoolLit(true)
      case _ =>
        t update subres
      }
    }
  }
}


object ContainsExplicitPointerVisitor {
  def apply(expr: IExpression): Boolean = {
    (new ContainsExplicitPointerVisitor)(expr)
  }

  class ContainsExplicitPointerVisitor
      extends CollectingVisitor[Unit, Boolean] {
    def apply(expr: IExpression): Boolean = {
      visit(expr, ())
    }
  
    private def isACSLFunction(fun: IFunction): Boolean = {
      ACSLExpression.functions.contains(fun)
    }
    private def isACSLPredicate(pred: Predicate): Boolean = {
      ACSLExpression.predicates.contains(pred)
    }
  
    override def preVisit(
        t: IExpression,
        dummy: Unit
    ): PreVisitResult = {
      t match {
        case IEquation(
          ConstantAsProgVarProxy(v1),
          ConstantAsProgVarProxy(v2))
            if v1.isPointer && v2.isPointer =>
          ShortCutResult(false)
        case TheoryOfHeapFunApp(_, _) =>
          ShortCutResult(false)
        case ACSLFunction(fun) =>
          ShortCutResult(false)
        case ACSLPredicate(pred) =>
          ShortCutResult(false)
        case IBinFormula(IBinJunctor.And, _, _) =>
          ShortCutResult(false)
        case _ =>
          KeepArg
      }
    }
  
    override def postVisit(
        t: IExpression,
        dummy: Unit,
        subres: Seq[Boolean]
    ): Boolean = t match {
      case ConstantAsProgVarProxy(v) if v.isPointer =>
        true
      case _ =>
        if (subres.isEmpty) false else subres.reduce(_ || _)
    }
  }
}


object TrivialEqualityRemover {
  def apply(expr: IExpression): IExpression = {
    (new TrivialEqualityRemover).visit(expr, ())
  }

  class TrivialEqualityRemover()
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
}


object HeapEqualityRemover {
  def apply(expr: IExpression, isCurrentHeap: ProgVarProxy => Boolean): IExpression = {
    (new HeapEqualityRemover(isCurrentHeap)).visit(expr, ())
  }

  class HeapEqualityRemover(isCurrentHeap: ProgVarProxy => Boolean)
      extends CollectingVisitor[Unit, IExpression] {
  
    override def postVisit(
        t: IExpression,
        dummy: Unit,
        subres: Seq[IExpression]
    ): IExpression = t match {
      case IEquation(ConstantAsProgVarProxy(left), _) if isCurrentHeap(left) =>
        IBoolLit(true)
      case IEquation(_, ConstantAsProgVarProxy(right)) if isCurrentHeap(right) =>
        IBoolLit(true)
      case _ =>
        t update subres
    }
  }
}
