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

/* PointerPropProcessor.scala
 * 
 * See PointerPropExtractor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 *
 * In this contract processor, any separation and validity clauses that can be 
 * deduced are extracted. This can only be done whenever the heap state is 
 * expressed.
 */

package tricera.postprocessor

import ap.parser._
import scala.collection.immutable.Stack
import tricera.{Solution, Invariant, HeapInfo, IFuncParam}
import tricera.FunctionInvariants
import tricera.concurrency.ccreader.CCExceptions.NeedsHeapModelException

object PointerPropProcessor extends ResultProcessor {
  // SSSOWO: TODO: Should heapInfo be part of constructor call instead?
  //   If it's done like that we don't have to check for a valid heap
  //   in the applyTo functions.
  //   The drawback is that we might apply a processor instantiated
  //   with the heap from one solution and apply it to another.

  override def applyTo(solution: Solution) = solution match {
    case Solution(functionInvariants, Some(heapInfo)) =>
      Solution(functionInvariants.map(applyTo(_, heapInfo)), Some(heapInfo))
    case _ =>
      throw NeedsHeapModelException
  }

  private def applyTo(funcInv: FunctionInvariants, heapInfo: HeapInfo)
  : FunctionInvariants = funcInv match {
    case FunctionInvariants(id, preCondition, postCondition, loopInvariants) =>
      FunctionInvariants(
        id,
        addPtrAtoms(preCondition, heapInfo),
        addPtrAtoms(postCondition, heapInfo),
        loopInvariants)
  }

  private def addPtrAtoms(invariant: Invariant, heapInfo: HeapInfo): Invariant = invariant match {
    case Invariant(form, srcInfo) =>
      val newForm = getSafePointers(form, heapInfo) match {
        case safePointers if safePointers.size >= 2 =>
          form
          .&(ACSLExpression.separatedPointers(safePointers))
          .&(ACSLExpression.validPointers(safePointers))
        case safePointers if safePointers.size == 1 =>
          form
          .&(ACSLExpression.validPointers(safePointers))
        case _ => 
          form
      }
      Invariant(newForm, srcInfo)
  }

  def getSafePointers(invForm: IFormula, heapInfo: HeapInfo): Set[IFuncParam] = {
    val valueSet = ValSetReader.invariant(invForm)
    val explForm = ToExplicitForm.invariant(invForm, valueSet)
    val redForm = HeapReducer(explForm, heapInfo)
    HeapExtractor(redForm, heapInfo) match {
      case Some(heap) =>
        val redValueSet = ValSetReader.invariant(redForm)
        readSafeVariables(heap, redValueSet)
      case _ => Set.empty[IFuncParam]
    }
  }

  def readSafeVariables(
      heap: HeapState,
      valueSetWithAddresses: ValSet
  ): Set[ISortedVariable] = {
    heap.storage.keys
      .flatMap(valueSetWithAddresses.getVariableForm(_))
      .asInstanceOf[Set[ISortedVariable]]
  }
}

object HeapExtractor {
  def apply(
      expr: IExpression,
      heapInfo: HeapInfo
  ): Option[HeapState] = {
    (new InvariantHeapExtractor(heapInfo)).visit(expr, ())
  }
}

class InvariantHeapExtractor(cci: HeapInfo)
    extends CollectingVisitor[Unit, Option[HeapState]] {
  override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
    case IEquation(h: IFuncParam, heap: HeapState) if cci.isCurrentHeap(h) =>
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

object HeapReducer {
  def apply(
      invariantExpression: IExpression,
      cci: HeapInfo
  ): IExpression = {
    (new HeapReducer(cci)).visit(invariantExpression, Stack[String]())
  }
}

class HeapReducer(cci: HeapInfo)
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
      case IFunApp(fun, args) if (fun.name == "emptyHeap" && args.isEmpty) => 
        HeapState.empty
      case ISortedVariable(index, sort) if sort.name == "Heap" => // TODO: Move magic constants to HeapInfo
        HeapState.heapById(quantifierIds(index))
      case TheoryOfHeapFunApp(
            writeFun,
            Seq(heap: HeapState, addr: Address, obj)
          ) if cci.isWriteFun(writeFun) =>
        heap.write(addr, obj.asInstanceOf[ITerm])
      case TheoryOfHeapFunApp(
            readFun,
            Seq(heap: HeapState, addr: Address)
          ) if cci.isReadFun(readFun) =>
        heap.read(addr)
      case TheoryOfHeapFunApp(
            allocFun,
            Seq(heap: HeapState, obj)
          ) if cci.isAllocFun(allocFun) =>
        heap.alloc(obj.asInstanceOf[ITerm])
      case TheoryOfHeapFunApp(newHeapFun, Seq(allocRes: AllocRes))
          if cci.isNewHeapFun(newHeapFun) =>
        allocRes.newHeap
      case TheoryOfHeapFunApp(newAddrFun, Seq(allocRes: AllocRes))
          if cci.isNewAddrFun(newAddrFun) =>
        allocRes.newAddr
      case _ => t update subres
    }
  }
}

/*
case class QuantifiedVarWithId(variable: ISortedVariable, id: String)
    extends ITerm {
  override def toString = {
    variable.toString + "(Q" + id.take(4) + ")"
  }
}

object ToInvariantFormVisitor
    extends CollectingVisitor[Stack[String], IExpression]
    with IdGenerator {

  def apply(contractCondition: IExpression): IExpression = {
    visit(contractCondition, Stack[String]())
  }

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
  ): IExpression = t match {
    case v @ ISortedVariable(index, sort) =>
      if (index < quantifierIds.size) { // quantified variable
        QuantifiedVarWithId(v, quantifierIds(index))
      } else {
        ISortedVariable(index - quantifierIds.size, sort)
      }
    case _ => t update (subres)
    // SSSOWO: Variables are shifted, but the IVariableBinder is
    //   never removed. Seems to me any binder in scope will bind
    //   new variables. Is this correct?
  }
}
*/