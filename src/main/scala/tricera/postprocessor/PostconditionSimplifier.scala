/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025-2026 Zafer Esen. All rights reserved.
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

/* PostconditionSimplifier.scala
 *
 * See PostconditionSimplifier in "Automated Inference of ACSL Contracts for
 * Programs with Heaps" by Oskar Söderberg
 *
 * In this contract processor, attempts are made to simplify the postcondition by
 * using the information in the precondition. This is done as the simplified
 * postcondition may contain more clauses that are directly expressible in ACSL.
 * The precondition is left unchanged.
 */

package tricera.postprocessor

import ap.parser._
import IExpression.{Conj, Disj, and, i, or}
import ap.SimpleAPI.ProverStatus
import ap.SimpleAPI.TimeoutException
import ap.theories._
import ap.SimpleAPI

import tricera._

object PostconditionSimplifier extends ResultProcessor {

  override def applyTo(solution : Solution) = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(simplifyPostCondition), loopInvariants)
  }

  private def simplifyPostCondition(funcInvs : FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(id,
                            isSrcAnnotated,
                            preCondition,
                            PostCondition(postInv),
                            loopInvariants) =>
      val newInvs = FunctionInvariants(
        id, isSrcAnnotated, preCondition,
        PostCondition(Invariant(
          simplify(postInv.expression,
                   asOldState(preCondition.invariant.expression)),
          postInv.heapInfo, postInv.sourceInfo)),
        loopInvariants)
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  // deref(p) in pre == oldDeref(p) in post
  private def asOldState(precondition : IFormula) : IFormula =
    OldStateVisitor.visit(precondition, ()).asInstanceOf[IFormula]

  private object OldStateVisitor extends CollectingVisitor[Unit, IExpression] {
    override def postVisit(t      : IExpression,
                           arg    : Unit,
                           subres : Seq[IExpression]) : IExpression =
      t update subres match {
        case IFunApp(fun, args) if fun == ACSLExpression.deref =>
          IFunApp(ACSLExpression.oldDeref, args)
        case updated => updated
      }
  }

  // Drop !pre in !pre | Q in post
  private def dropPreconditionGuard(postcondition : IFormula,
                                    precondition  : IFormula) : IFormula = {
    val preConjs = LineariseVisitor(precondition, IBinJunctor.And).toSet
    val kept = LineariseVisitor(postcondition, IBinJunctor.Or).filterNot {
      case INot(f) =>
        LineariseVisitor(f, IBinJunctor.And).forall(preConjs.contains)
      case _ => false
    }
    if (kept.isEmpty) postcondition else or(kept)
  }

  private def simplify(postcondition : IFormula,
                       precondition  : IFormula) : IFormula = {

    val postConjs =
      LineariseVisitor(
        Transform2NNF(dropPreconditionGuard(postcondition, precondition)),
        IBinJunctor.And)
    // The reason we partition the conjuncts based on heap operations is that we
    // would like to preserve non-heap conjuncts even if they are implied by a
    // formula involving heap operations.
    // Example:
    // valid(p) & h' = write(h, p, y) & read(h', p) = x & x = y
    // We would like to preserve the conjunct x = y, but that is implied by the
    // read-over-write axiom of the theory of heaps. We simplify heap conjuncts
    // using non-heap conjuncts though.
    val (postHeapConjs, otherConjs) =
      postConjs.partition(c => HeapFunDetector(c))
    val simpHeap  = simplifyHelper(and(postHeapConjs),
                                   precondition &&& and(otherConjs))
    simpHeap &&& and(otherConjs)
  }

  private def simplifyHelper(f       : IFormula,
                             context : IFormula) : IFormula = {
    if (isImplied(context, f)) {
      IBoolLit(true)
    } else if (isImplied(context, !f)) {
      i(false)
    } else f match {
      case Conj(f1, f2) =>
        val s1 = simplifyHelper(f1, context)
        if (s1 == i(false)) i(false)
        else s1 &&& simplifyHelper(f2, context &&& s1)
      case Disj(f1, f2) =>
        val s1 = simplifyHelper(f1, context)
        if (s1 == IBoolLit(true)) IBoolLit(true)
        else s1 ||| simplifyHelper(f2, context &&& !s1)
      case Disj(INot(f1), f2) =>
        val s1 = simplifyHelper(f1, context)
        if (s1 == i(false)) IBoolLit(true)
        else s1 ===> simplifyHelper(f2, context &&& s1)
      case INot(f) => !simplifyHelper(f, context)
      case _ => f
    }
  }

  private def isImplied(context : IFormula, formula : IFormula) : Boolean = {
    SimpleAPI.withProver { p =>
      import p._
      // check if context && !formula is UNSAT
      val combinedFormula = context &&& !formula
      addConstants(SymbolCollector constantsSorted combinedFormula)
      addRelations(ACSLExpression.predicatesSorted)
      ACSLExpression.functionsSorted.foreach(f => addFunction(f))

      val theoryCollector = new TheoryCollector
      theoryCollector(combinedFormula)
      addTheories(theoryCollector.theories)
      addAssertion(combinedFormula)

      try {
        withTimeout(100) {
          ??? match {
            case ProverStatus.Unsat => true
            case _ => false
          }
        }
      } catch {
        case x: SimpleAPI.SimpleAPIException if x == TimeoutException =>
          false
      }
    }
  }

  private object HeapFunDetector {
    def apply(f : IFormula) : Boolean = {
      val visitor = new HeapFunDetector
      visitor.visit(f, ())
      visitor.hasHeap
    }
  }
  private class HeapFunDetector extends CollectingVisitor[Unit, Unit] {
    var hasHeap = false
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = t match {
      case IFunApp(function @ Heap.HeapRelatedFunction(heap), _)
        if heap.functions.contains(function) =>
        //  heap.functions.contains(function) excludes functions allocResHeap
        //  and allocResAddr, but those should not be appearing in results
        hasHeap = true
        ShortCutResult()
      case IAtom(predicate @ Heap.HeapRelatedPredicate(heap), _)
        if heap.predicates.contains(predicate) =>
        hasHeap = true
        ShortCutResult()
      case _ => KeepArg
    }
    override def postVisit(t      : IExpression,
                           arg    : Unit,
                           subres : Seq[Unit]) : Unit = {}
  }
}
