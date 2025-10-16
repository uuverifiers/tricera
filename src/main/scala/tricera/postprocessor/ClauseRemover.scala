/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025 Scania CV AB. All rights reserved.
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

import ap.parser.IExpression.{Conj, Disj}
import ap.parser._
import tricera._
import tricera.Util.FSharpisms

object ClauseRemover extends ResultProcessor {
  override def applyTo(solution: Solution): Solution = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(applyTo), loopInvariants)
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
      Invariant(
        expression
          .through(e => CleanupVisitor(TheoryOfHeapRemoverVisitor(e, heapInfo)))
          .through(e => CleanupVisitor(ExplicitPointerRemover(e)))
          .through(e => CleanupVisitor(TrivialEqualityRemover(e)))
          .through(e => CleanupVisitor(HeapEqualityRemover(e, isCurrentHeap))
          .asInstanceOf[IFormula]),
        Some(heapInfo),
        sourceInfo)
    case Invariant(expression, None, sourceInfo) => 
      val newForm = CleanupVisitor(TrivialEqualityRemover(expression)).asInstanceOf[IFormula]
      Invariant(newForm, None, sourceInfo)
  }
}


object TheoryOfHeapRemoverVisitor {
  def apply(expr: IExpression, heapInfo: HeapInfo): IExpression = {
    (new TheoryOfHeapRemoverVisitor(heapInfo)).visit(expr, ())
  }

  class TheoryOfHeapRemoverVisitor(heapInfo: HeapInfo)
    extends CollectingVisitor[Unit, IExpression] {

    override def postVisit(t      : IExpression,
                           dummy  : Unit,
                           subres : Seq[IExpression]) : IExpression = t match {
      case form @ IBinFormula(_, _, _) =>
        postVisitFormula(form, subres, heapInfo)
      case q @ ISortedQuantified(_, _, _) =>
        subres(0) match {
          case IBoolLit(true) => IBoolLit(true)
          case _ => q update subres
        }
      case _ if ContainsTOHVisitor(t, heapInfo) =>
        IBoolLit(true)
      case _ =>
        t update subres
    }

    private def postVisitFormula(form: IFormula, subres: Seq[IExpression], heapInfo: HeapInfo)
    : IExpression = form match {
      case Conj(IBoolLit(true), IBoolLit(true))
         | Disj(IBoolLit(true), _)
         | Disj(_, IBoolLit(true))
         | IBinFormula(IBinJunctor.Eqv, IBoolLit(true), _)
         | IBinFormula(IBinJunctor.Eqv, _, IBoolLit(true)) =>
        // Either or both sides were already true before traversal
        IBoolLit(true)
      case IBinFormula(IBinJunctor.Eqv, preLhs, preRhs) =>
        // Neither side was true before traversal
        (subres(0), subres(1)) match {
          case (IBoolLit(true), _)
             | (_, IBoolLit(true)) =>
            // Either or both sides where removed during traversal
            IBoolLit(true)
          case _ =>
            // Neither side was removed during traversal
            form update subres
        }
      case Disj(preLhs, preRhs) =>
        // Neither side was true before traversal
        val lhs = subres(0)
        val rhs = subres(1)
        (lhs, rhs) match {
          case (IBoolLit(true), IBoolLit(true)) =>
            // Both sides were removed during traversal
            IBoolLit(true)
          case (IBoolLit(true), _) =>
            // LHS has been removed
            rhs
          case (_, IBoolLit(true)) =>
            // RHS has been removed
            lhs
          case _ => 
            // Neither side was removed during traversal
            form update subres
        }
      case Conj(IBoolLit(true), _) =>
        // LHS was true before traversal
        val rhs = subres(1)
        rhs
      case Conj(_, IBoolLit(true)) =>
        // RHS was true before traversal
        val lhs = subres(0)
        lhs
      case Conj(preLhs, preRhs) =>
        // Neither side was true before traversal
        val lhs = subres(0)
        val rhs = subres(1)
        (lhs, rhs) match {
          case (IBoolLit(true), IBoolLit(true)) =>
            // Both sides were removed during traversal
            IBoolLit(true)
          case (IBoolLit(true), _) =>
            // LHS was removed during traversal
            rhs
          case (_, IBoolLit(true)) =>
            // RHS was removed during traversal
            lhs
          case _ =>
            // Neither side was removed during traversal
            form update subres
        }
      case _ =>
        form update subres
    }
  }
}


object ContainsTOHVisitor {
  def apply(expr: IExpression, heapInfo: HeapInfo): Boolean = {
    (new ContainsTOHVisitor(heapInfo))(expr)
  }

  class ContainsTOHVisitor(heapInfo: HeapInfo)
      extends CollectingVisitor[Unit, Boolean] {
  
    def apply(expr: IExpression): Boolean = {
      visit(expr, ())
    }
  
    override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
      case TheoryOfHeapFunApp(_, _) =>
        ShortCutResult(true)
      case IFunApp(fun, _)
        if heapInfo.isObjSelector(fun) || heapInfo.isObjCtor(fun) =>
        ShortCutResult(true)
      case Is_O_Sort(_) =>
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
        case Conj(_, _) =>
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
