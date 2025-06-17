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

/* PointerPropProcessor.scala
 * 
 * See PointerPropExtractor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 */

package tricera.postprocessor

import ap.parser._
import scala.collection.immutable.Stack
import tricera.{
  ConstantAsProgVarProxy, FunctionInvariants, HeapInfo, Invariant, InvariantContext,
  PostCondition, PreCondition, ProgVarProxy, Result, Solution}
import tricera.concurrency.ccreader.CCExceptions.NeedsHeapModelException
import tricera.CounterExample
import tricera.LoopInvariant


case class SafePointers(
  id: String,
  preCondPointers: Set[ProgVarProxy],
  postCondPointers: Set[ProgVarProxy])


object SafePointerExtractor {
  def apply(result: Result): Seq[SafePointers] = result match {
    case Solution(functionInvariants, _) => functionInvariants.map(applyTo)
    case _ => Seq[SafePointers]()
  }

  private def applyTo(funcInvs: FunctionInvariants)
  : SafePointers = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      preCond @ PreCondition(preInv),
      postCond @ PostCondition(postInv),
      loopInvariants) =>
      SafePointers(
        id,
        getSafePointers(preInv, preCond.isCurrentHeap),
        getSafePointers(postInv, postCond.isCurrentHeap))
  }

  def getSafePointers(
    invariant: Invariant,
    isCurrentHeap: ProgVarProxy => Boolean)
    : Set[ProgVarProxy] = invariant match {
    case Invariant(form, Some(heapInfo), srcInfo) =>
      getSafePointers(form, heapInfo, isCurrentHeap)
    case _ =>
      Set[ProgVarProxy]()
  }

  private def getSafePointers(invForm: IFormula, heapInfo: HeapInfo, isCurrentHeap: ProgVarProxy => Boolean): Set[ProgVarProxy] = {
    val valueSet = ValSetReader.invariant(invForm)
    val explForm = ToExplicitForm.invariant(invForm, valueSet, isCurrentHeap)
    val redForm = HeapReducer(explForm, heapInfo)
    HeapExtractor(redForm, isCurrentHeap) match {
      case Some(heap) =>
        val redValueSet = ValSetReader.invariant(redForm)
        readSafeVariables(heap, redValueSet)
      case _ => Set.empty[ProgVarProxy]
    }
  }

  private def readSafeVariables(
      heap: HeapState,
      valueSetWithAddresses: ValSet
  ): Set[ProgVarProxy] = {
    heap.storage.keys
      .flatMap(
        valueSetWithAddresses.getVariableForm(_) match {
          case Some(ConstantAsProgVarProxy(p)) => Some(p)
          case None => None
        }
      )
      .asInstanceOf[Set[ProgVarProxy]]
  }
}

private object HeapExtractor {
  def apply(
      expr: IExpression,
      isCurrentHeap: ProgVarProxy => Boolean
  ): Option[HeapState] = {
    (new InvariantHeapExtractor(isCurrentHeap)).visit(expr, ())
  }
}

private class InvariantHeapExtractor(isCurrentHeap: ProgVarProxy => Boolean)
    extends CollectingVisitor[Unit, Option[HeapState]] {
  override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
    case IEquation(ConstantAsProgVarProxy(h), heap: HeapState) if isCurrentHeap(h) =>
      ShortCutResult(Some(heap))
    case _ =>
      KeepArg
  }

  override def postVisit(
      t: IExpression,
      arg: Unit,
      subres: Seq[Option[HeapState]]
  ): Option[HeapState] = t match {
    case h: HeapState => Some(h)
    case _            => subres.collectFirst { case Some(h) => h }
  }
}

private object HeapReducer {
  def apply(
      invariantExpression: IExpression,
      heapInfo: HeapInfo
  ): IExpression = {
    (new HeapReducer(heapInfo)).visit(invariantExpression, Stack[String]())
  }
}

private class HeapReducer(heapInfo: HeapInfo)
    extends CollectingVisitor[Stack[String], IExpression]
    with IdGenerator {

  override def preVisit(
      t: IExpression,
      quantifierIds: Stack[String]
  ): PreVisitResult = t match {
    case v: IVariableBinder => UniSubArgs(quantifierIds.push(generateId))
    case _                  => KeepArg
  }

  override def postVisit(
      t: IExpression,
      quantifierIds: Stack[String],
      subres: Seq[IExpression]
  ): IExpression = {
    t update subres match {
      case IFunApp(
            fun,
            args
          ) if (heapInfo.isEmptyHeapFun(fun) && args.isEmpty) => 
        HeapState.empty
      case ISortedVariable(
            index,
            sort
          ) if heapInfo.isHeapSortName(sort.name) =>
        HeapState.heapById(quantifierIds(index))
      case IFunApp(
            writeFun,
            Seq(heap: HeapState, addr: Address, obj)
          ) if heapInfo.isWriteFun(writeFun) =>
        heap.write(addr, obj.asInstanceOf[ITerm])
      case IFunApp(
            readFun,
            Seq(heap: HeapState, addr: Address)
          ) if heapInfo.isReadFun(readFun) =>
        heap.read(addr)
      case IFunApp(
            allocFun,
            Seq(heap: HeapState, obj)
          ) if heapInfo.isAllocFun(allocFun) =>
        heap.alloc(obj.asInstanceOf[ITerm])
      case IFunApp(
            newHeapFun,
            Seq(allocRes: AllocRes)
          ) if heapInfo.isNewHeapFun(newHeapFun) =>
        allocRes.newHeap
      case IFunApp(
            newAddrFun,
            Seq(allocRes: AllocRes)
          ) if heapInfo.isNewAddrFun(newAddrFun) =>
        allocRes.newAddr
      case _ => t update subres
    }
  }
}
