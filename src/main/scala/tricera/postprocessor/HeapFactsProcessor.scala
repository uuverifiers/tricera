/**
 * Copyright (c) 2026 Zafer Esen. All rights reserved.
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
import ap.terfor.conjunctions.Quantifier
import IExpression.{Conj, Eq, i}
import tricera._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * Adds heap facts to preconditions to be used in later stages.
 * Heap facts are extracted from alloc/write chains, addresses, heap sizes etc.
 */
object HeapFactsProcessor extends ResultProcessor {
  override def applyTo(solution : Solution) : Solution = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(applyTo), loopInvariants)
  }

  private def applyTo(funcInvs : FunctionInvariants) : FunctionInvariants =
    funcInvs.preCondition.invariant match {
      case Invariant(form, Some(heapInfo), srcInfo) =>
        val facts = ChainFactsReader(form, heapInfo)
        if (facts.isEmpty) funcInvs
        else {
          val newInvs = funcInvs.copy(preCondition = PreCondition(Invariant(
            facts.foldLeft(form)(_ & _), Some(heapInfo), srcInfo)))
          DebugPrinter.oldAndNew(this, funcInvs, newInvs)
          newInvs
        }
      case _ => funcInvs
    }
}

private object ChainFactsReader {
  def apply(form : IFormula, heapInfo : HeapInfo) : Seq[IFormula] =
    (new ChainFactsReader(heapInfo)).factsOf(form)
}

private class ChainFactsReader(heapInfo : HeapInfo) {
  private val addrNumberOfTerm = new mutable.LinkedHashMap[ITerm, Int]
  private val heapChains = new ArrayBuffer[(ITerm, Int, Seq[(ITerm, ITerm)])]

  def factsOf(form : IFormula) : Seq[IFormula] = {
    collect(form)

    val addrFacts =
      for ((term, addrNumber) <- addrNumberOfTerm.toSeq)
        yield Eq(term, addrTerm(addrNumber))

    val chainFacts = heapChains.flatMap { case (heapVar, allocCount, writes) =>
      //size only depends on the alloc count, can always be added
      val sizeFact = heapInfo.heapSizeFun.map(
        sizeFun => Eq(IFunApp(sizeFun, Seq(heapVar)), i(allocCount))).toSeq
      sizeFact ++ readFacts(heapVar, writes)
    }

    addrFacts ++ chainFacts
  }

  // only sound if every written address is known (otherwise may alias)
  private def readFacts(heapVar : ITerm,
                        writes  : Seq[(ITerm, ITerm)]) : Seq[IFormula] = {
    val resolved = writes.map {
      case (addr, obj) => (resolveAddrNumber(addr), addr, obj) }
    if (!resolved.forall(_._1.isDefined)) return Seq()

    val lastWrites = new mutable.LinkedHashMap[Int, (ITerm, ITerm)]
    for ((Some(addrNumber), addr, obj) <- resolved)
      lastWrites(addrNumber) = (addr, obj)

    for ((_, (addr, obj)) <- lastWrites.toSeq;
         if !HasVariable(addr) && !HasVariable(obj))
    yield Eq(IFunApp(heapInfo.heap.read, Seq(heapVar, addr)), obj)
  }

  // only positive conjuncts imply anything (not disj or neg)
  // collecting under EX is also fine, the facts never mention bound variables
  private def collect(f: IFormula): Unit = f match {
    case Conj(f1, f2) =>
      collect(f1); collect(f2)
    case IQuantified(Quantifier.EX, sub) =>
      collect(sub)
    case Eq(lhs, rhs) =>
      collectAddrEquality(lhs, rhs); collectAddrEquality(rhs, lhs)
      collectHeapChain(lhs, rhs); collectHeapChain(rhs, lhs)
    case _ => ()
  }

  // collects term = <address of the k-th allocation>
  private def collectAddrEquality(term          : ITerm,
                                  allocAddrTerm : ITerm) : Unit =
    allocatedAddrNumber(allocAddrTerm) match {
      case Some(k) if !HasVariable(term) &&
                      resolveAddrNumber(term).isEmpty =>
        addrNumberOfTerm(term) = k
      case _ => ()
    }

  // collects <pre-state heap variable> = <alloc/write chain>
  private def collectHeapChain(heapVar   : ITerm,
                               chainTerm : ITerm) : Unit =
    heapVar match {
      case IConstant(p: ProgVarProxy)
          if heapInfo.isHeap(p) && p.isPreExec =>
        for ((allocCount, writes) <- chain(chainTerm))
          heapChains += ((heapVar, allocCount, writes))
      case _ => ()
    }

  // the k-th alloc from the empty heap yields address k
  private def chain(term : ITerm) : Option[(Int, Seq[(ITerm, ITerm)])] =
    term match {
      case IFunApp(f, Seq()) if heapInfo.isEmptyHeapFun(f) =>
        Some((0, Vector()))
      case Allocation(heapBefore, obj) =>
        chain(heapBefore).map { case (allocCount, writes) =>
          (allocCount + 1, writes :+ (addrTerm(allocCount + 1), obj)) }
      case IFunApp(f, Seq(heapBefore: ITerm, addr: ITerm, obj: ITerm))
          if heapInfo.isWriteFun(f) =>
        chain(heapBefore).map { case (allocCount, writes) =>
          (allocCount, writes :+ (addr, obj)) }
      case _ => None
    }

  // newHeap(alloc(h, obj)) or allocHeap(h, obj)
  private object Allocation {
    def unapply(term : ITerm) : Option[(ITerm, ITerm)] = term match {
      case IFunApp(f1, Seq(IFunApp(f2, Seq(heapBefore: ITerm, obj: ITerm))))
          if heapInfo.isNewHeapFun(f1) && heapInfo.isAllocFun(f2) =>
        Some((heapBefore, obj))
      case IFunApp(f, Seq(heapBefore: ITerm, obj: ITerm))
          if heapInfo.isAllocHeapFun(f) =>
        Some((heapBefore, obj))
      case _ => None
    }
  }

  // newAddr(alloc(h, obj)) or allocAddr(h, obj)
  private object AllocationAddr {
    def unapply(term : ITerm) : Option[ITerm] = term match {
      case IFunApp(f1, Seq(IFunApp(f2, Seq(heapBefore: ITerm, _))))
          if heapInfo.isNewAddrFun(f1) && heapInfo.isAllocFun(f2) =>
        Some(heapBefore)
      case IFunApp(f, Seq(heapBefore: ITerm, _))
          if heapInfo.isAllocAddrFun(f) =>
        Some(heapBefore)
      case _ => None
    }
  }

  private def allocatedAddrNumber(term : ITerm) : Option[Int] = term match {
    case AllocationAddr(heapBefore) => chain(heapBefore).map(_._1 + 1)
    case _ => None
  }

  private def resolveAddrNumber(term : ITerm) : Option[Int] = term match {
    case IFunApp(f, Seq(IIntLit(k))) if heapInfo.isAddrFun(f) =>
      Some(k.intValueSafe)
    case _ =>
      allocatedAddrNumber(term).orElse(addrNumberOfTerm.get(term))
  }

  private def addrTerm(addrNumber : Int) : ITerm =
    IFunApp(heapInfo.heap.addr, Seq(i(addrNumber)))

  private object HasVariable extends CollectingVisitor[Unit, Boolean] {
    def apply(t: IExpression): Boolean = visit(t, ())
    override def postVisit(t: IExpression,
                           arg: Unit,
                           subres: Seq[Boolean]): Boolean =
      t.isInstanceOf[IVariable] || subres.contains(true)
  }
}
