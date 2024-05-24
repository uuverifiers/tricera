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

object PointerPropProcessor extends ContractProcessor with ClauseCreator {
  def processContractCondition(cci: ContractConditionInfo) = {
    getSafePointers(cci.contractCondition, cci) match {
      case safePointers if safePointers.size >= 2 =>
        cci.contractCondition
          .&(ACSLExpression.separatedPointers(safePointers, 0, cci))
          .&(ACSLExpression.validPointers(safePointers, 0, cci))
      case _ => 
        cci.contractCondition
    }
  }

  def getClauses(expr: IExpression, cci: ContractConditionInfo): Option[IFormula] = {
    getSafePointers(expr, cci) match {
        case safePointers if safePointers.size >= 2 =>
          Some(ACSLExpression.separatedPointers(safePointers, 0, cci)
            .&(ACSLExpression.validPointers(safePointers, 0, cci)))
        case safePointers if safePointers.size == 1 =>
          Some(ACSLExpression.validPointers(safePointers, 0, cci))
        case _ => 
            None
    }
  }

  def getSafePointers(expr: IExpression, cci: ContractConditionInfo): Set[ISortedVariable] = {
    val invForm = ToInvariantFormVisitor(expr)
    val valueSet = ValSetReader.invariant(invForm)
    val explForm = ToExplicitForm.invariant(invForm, valueSet, cci)
    val redForm = HeapReducer(explForm, cci)
    HeapExtractor(redForm, cci) match {
      case Some(heap) =>
        val redValueSet = ValSetReader.invariant(redForm)
        readSafeVariables(heap, redValueSet)
      case _ => Set.empty[ISortedVariable]
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
      cci: ContractConditionInfo
  ): Option[HeapState] = {
    (new InvariantHeapExtractor(cci)).visit(expr, ())
  }
}

class InvariantHeapExtractor(cci: ContractConditionInfo)
    extends CollectingVisitor[Unit, Option[HeapState]] {
  override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
    case IEquation(h: ISortedVariable, heap: HeapState) if cci.isCurrentHeap(h, 0) =>
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
      cci: ContractConditionInfo
  ): IExpression = {
    (new HeapReducer(cci)).visit(invariantExpression, Stack[String]())
  }
}

class HeapReducer(cci: ContractConditionInfo)
    extends CollectingVisitor[Stack[String], IExpression] {

  override def postVisit(
      t: IExpression,
      quantifierIds: Stack[String],
      subres: Seq[IExpression]
  ): IExpression = {
    t update subres match {
      case QuantifiedVarWithId(ISortedVariable(_, sort), id)
          if sort.name == "Heap" =>
        HeapState.heapById(id)
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
  }
}
