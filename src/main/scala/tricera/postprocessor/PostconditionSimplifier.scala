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
 * Expanded array-heap reads are also normalised in the precondition.
 */

package tricera.postprocessor

import ap.parser._
import IExpression.{Conj, Disj, and, i, or, toFunApplier}
import ap.SimpleAPI.ProverStatus
import ap.SimpleAPI.TimeoutException
import ap.theories._
import ap.SimpleAPI

import tricera._
import tricera.concurrency.CCReader
import tricera.concurrency.ccreader.{CCHeapPointer, CCHeapArrayPointer}

object PostconditionSimplifier extends ResultProcessor {

  // use valid(p) in pre to simplify e.g. !is_int(read(old_heap, p)) || P to P.
  def usingValidityRequirements(result : Result, reader : CCReader) : Result = result match {
    case solution : Solution =>
      val printed = AddValidPointerPredicates.applyTo(
        RewrapPointers.applyTo(ClauseRemover.applyTo(solution)))
      val contexts = reader.getFunctionContexts
      solution.copy(functionInvariants = solution.functionInvariants.zip(
        printed.functionInvariants).map { case (inv, translated) =>
        val pre = inv.preCondition.invariant
        val post = inv.postCondition.invariant
        val facts = for {
          info <- post.heapInfo.toSeq
          context <- contexts.get(inv.id).toSeq.map(_.acslContext)
          heap <- SymbolCollector.constants(pre.expression & post.expression).collect {
            case p : ProgVarProxy if inv.preCondition.isCurrentHeap(p) => IConstant(p)
          }.toSeq
          IAtom(ACSLExpression.valid, Seq(IConstant(p : ProgVarProxy))) <-
            LineariseVisitor(translated.preCondition.invariant.expression, IBinJunctor.And)
          if p.isPreExec && (p.isParameter || p.isGlobal)
          v <- (if (p.isParameter) context.getParams else context.getGlobals)
            .filter(_.name == p.name)
          location <- v.typ match {
            case t : CCHeapPointer => Some((IConstant(p) : ITerm, t.typ.toSort))
            case t : CCHeapArrayPointer => Some((info.heap.rangeNth(
              t.ptrOps.getRange(IConstant(p)), t.ptrOps.getOffset(IConstant(p))),
              t.elementType.toSort))
            case _ => None
          }
          if context.sortWrapper(location._2).isDefined
        } yield info.heap.hasUserHeapCtor(
          info.heap.read(heap, location._1), context.getCtor(location._2))
        if (facts.isEmpty) inv
        else {
          val known = facts.flatMap(IExpression.EqLit.unapply).toMap
          val simplified = Rewriter.rewrite(post.expression, {
            case IExpression.EqLit(t, n) if known.get(t).contains(n) => IBoolLit(true)
            case e => e
          }).asInstanceOf[IFormula]
          if (simplified == post.expression) inv
          else inv.copy(postCondition = PostCondition(post.copy(expression =
            new Simplifier().apply(simplified))))
        }
      })
    case _ => result
  }

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
      val preInv = preCondition.invariant
      val newInvs = FunctionInvariants(
        id, isSrcAnnotated,
        PreCondition(Invariant(
          normaliseHeapReads(preInv.expression, preInv.expression, preInv.heapInfo),
          preInv.heapInfo, preInv.sourceInfo)),
        PostCondition(Invariant(
          simplify(postInv.expression,
                   asOldState(preCondition.invariant.expression), postInv.heapInfo),
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
                       precondition  : IFormula,
                       heapInfo      : Option[HeapInfo]) : IFormula = {

    val normalised = reduceArithmeticUsingPrecondition(postcondition, precondition)
    val postConjs =
      LineariseVisitor(
        Transform2NNF(dropPreconditionGuard(normalised, precondition)),
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
      postConjs.partition(c => HeapFunDetector(c, heapInfo))
    val simpHeap = simplifyHelper(and(postHeapConjs), precondition &&& and(otherConjs))
    val simplified = simpHeap &&& and(otherConjs)
    normaliseHeapReads(simplified, precondition, heapInfo)
  }

  // use e.g. n = 3 to simplify x + n - 3 into x
  private def reduceArithmeticUsingPrecondition(form : IFormula, pre : IFormula) : IFormula =
    SimpleAPI.withProver { p =>
      import ap.terfor.equations.{EquationConj, ReduceWithEqs}
      import ap.terfor.linearcombination.LinearCombination
      p.addConstants(SymbolCollector.constantsSorted(pre & form))
      val collector = new TheoryCollector
      collector(pre & form)
      p.addTheories(collector.theories)
      ACSLExpression.functionsSorted.foreach(p.addFunction(_))
      p.addRelations(ACSLExpression.predicatesSorted)
      val equations = LineariseVisitor(pre, IBinJunctor.And).flatMap { conjunct =>
        p.asConjunction(conjunct).arithConj.positiveEqs.iterator
      }
      val assumptions = EquationConj(equations, p.order)
      if (assumptions.isTrue || assumptions.isFalse) form
      else {
        val reduce = ReduceWithEqs(assumptions, p.order)
        Rewriter.rewrite(form, {
          case t : ITerm if (t.isInstanceOf[IPlus] || t.isInstanceOf[ITimes]) &&
              !ContainsSymbol(t, {
                case _ : IPlus | _ : ITimes | _ : IConstant | _ : IIntLit => false
                case _ => true
              }) =>
            val linear = InputAbsy2Internal(t, p.order).asInstanceOf[LinearCombination]
            val reduced = reduce(linear)
            if (reduced == linear) t else Internal2InputAbsy(reduced)
          case e => e
        }).asInstanceOf[IFormula]
      }
    }

  private def normaliseHeapReads(form: IFormula, pre: IFormula,
                                 heapInfo: Option[HeapInfo]): IFormula =
    heapInfo.map(_.heap) match {
      case Some(heap: ap.theories.heaps.ArrayHeap) =>
        normaliseArrayHeapReads(form, pre, heap)
      case _ => form
    }

  private def normaliseArrayHeapReads(post: IFormula, pre: IFormula,
                                  heap: ap.theories.heaps.ArrayHeap): IFormula = {
    import IExpression._
    val sizes: Map[ITerm, ITerm] = LineariseVisitor(pre, IBinJunctor.And).flatMap {
      case DiffEq(size @ IFunApp(f, _), start @ IFunApp(g, _), n)
          if f == heap.heapSize && g == heap.rangeStart =>
        Some(size -> (start + n))
      case DiffEq(start @ IFunApp(g, _), size @ IFunApp(f, _), n)
          if f == heap.heapSize && g == heap.rangeStart =>
        Some(size -> (start - n))
      case _ => None
    }.toMap
    val context = pre & post
    val visitor = new CollectingVisitor[Unit, IExpression] {
      override def postVisit(t: IExpression, arg: Unit,
                             subres: Seq[IExpression]): IExpression =
        (t update subres) match {
          case read @ IFunApp(select, Seq(IFunApp(contents, Seq(h)), index))
              if select == heap.arrayTheory.select && contents == heap.heapContents &&
                SymbolCollector.variables(read).isEmpty =>
            val resolvedIndex = Rewriter.rewrite(index, {
              case t: ITerm if sizes.contains(t) => sizes(t)
              case e => e
            }).asInstanceOf[ITerm]
            val address = heap.addr(new Simplifier().apply(resolvedIndex))
            if (isImplied(context, heap.isAlloc(h, address)))
              heap.read(h, address)
            else read
          case updated => updated
        }
    }
    visitor.visit(post, ()).asInstanceOf[IFormula]
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
    def apply(f: IFormula, heapInfo: Option[HeapInfo]): Boolean = {
      val visitor = new HeapFunDetector(heapInfo)
      visitor.visit(f, ())
      visitor.hasHeap
    }
  }
  private class HeapFunDetector(heapInfo: Option[HeapInfo])
      extends CollectingVisitor[Unit, Unit] {
    var hasHeap = false
    override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
      case IFunApp(function @ Heap.HeapRelatedFunction(heap), _)
          if heap.functions.contains(function) =>
        hasHeap = true
        ShortCutResult()
      case IAtom(predicate @ Heap.HeapRelatedPredicate(heap), _)
          if heap.predicates.contains(predicate) =>
        hasHeap = true
        ShortCutResult()
      case IFunApp(function, _) if heapInfo.exists(_.heap match {
        case h: ap.theories.heaps.ArrayHeap =>
          function == h.heapContents || function == h.heapSize || function == h.heapPair
        case _ => false
      }) =>
        hasHeap = true
        ShortCutResult()
      case _ => KeepArg
    }
    override def postVisit(t      : IExpression,
                           arg    : Unit,
                           subres : Seq[Unit]) : Unit = {}
  }
}
