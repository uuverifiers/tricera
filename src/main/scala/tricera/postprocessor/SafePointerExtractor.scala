/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025 Scania CV AB
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

/* PointerPropProcessor.scala
 * 
 * See PointerPropExtractor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 */

package tricera.postprocessor

import ap.parser._
import ap.theories.ADT
import tricera._

object SafePointerExtractor {
  def getSafePointers(invariant     : Invariant,
                      isCurrentHeap : ProgVarProxy => Boolean) : ValSet =
    invariant match {
      case Invariant(form, Some(heapInfo), _) =>
        getSafePointers(form, heapInfo, isCurrentHeap)
      case _ => ValSet.empty
    }

  private def getSafePointers(
    invForm       : IFormula,
    heapInfo      : HeapInfo,
    isCurrentHeap : ProgVarProxy => Boolean) : ValSet = {
    @scala.annotation.tailrec
    def reduce(form: IExpression, remaining: Int): IExpression = {
      if (remaining == 0) form
      else {
        val next = HeapReducer(form, heapInfo, ValSetReader(form))
        if (next == form) form else reduce(next, remaining - 1)
      }
    }
    val redForm = reduce(invForm, SymbolCollector.constants(invForm).size + 1)
    HeapExtractor(redForm, isCurrentHeap) match {
      case Some(heap) =>
        val redValueSet = ValSetReader(redForm)
        readSafeVariables(heap, redValueSet, heapInfo)
      case _ => ValSet.empty
    }
  }

  private def readSafeVariables(heap                  : HeapState,
                                valueSetWithAddresses : ValSet,
                                heapInfo : HeapInfo) : ValSet = {
    val addresses = heap.storage.collect {
      case (address, IFunApp(ctor, _))
          if heapInfo.objectCtorToSelector(ctor).nonEmpty => address
    }
    ValSet(addresses.map(valueSetWithAddresses.getVariantVariables).toSet)
  }

  def getValidPointers(invariant : Invariant,
                       isCurrentHeap : ProgVarProxy => Boolean) : Set[ProgVarProxy] =
    invariant.heapInfo.map { info =>
      def collect(form : IFormula, values : ValSet) : Set[ProgVarProxy] = {
        def pointers(heap : ITerm, address : ITerm) : Set[ProgVarProxy] = {
          val heaps = values.getVal(heap).map(_.variants).getOrElse(Set(heap))
          if (!heaps.exists {
            case ConstantAsProgVarProxy(p) => isCurrentHeap(p)
            case _ => false
          }) Set.empty
          else (values.getVal(address).map(_.variants).getOrElse(Set(address))).collect {
            case ConstantAsProgVarProxy(p) if p.isPointer => p
          }
        }
        def fromObject(term : ITerm) : Set[ProgVarProxy] = term match {
          case IFunApp(read, Seq(heap, address)) if info.isReadFun(read) =>
            pointers(heap, address)
          case _ => Set.empty
        }
        form match {
          case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sort), Seq(obj)), id) =>
            adt.constructors.filter(_.resSort == adt.sorts(sort))
              .lift(id.intValueSafe).filter(c =>
              info.objectCtorToSelector(c).nonEmpty).map(_ => fromObject(obj))
              .getOrElse(Set.empty)
          case IEquation(obj, IFunApp(ctor, _))
              if info.objectCtorToSelector(ctor).nonEmpty => fromObject(obj)
          case IEquation(IFunApp(ctor, _), obj)
              if info.objectCtorToSelector(ctor).nonEmpty => fromObject(obj)
          case IBinFormula(IBinJunctor.And, left, right) =>
            collect(left, values) ++ collect(right, values)
          case IBinFormula(IBinJunctor.Or, left, right) =>
            collect(left, ValSet.union(values, ValSetReader(left))) intersect
              collect(right, ValSet.union(values, ValSetReader(right)))
          case IQuantified(IExpression.Quantifier.EX, body) =>
            collect(body, ValSetReader(body))
          case _ => Set.empty
        }
      }
      val form = ToVariableForm.normaliseReadAddresses(invariant.expression,
        ValSetReader(invariant.expression), invariant.heapInfo)
      collect(form, ValSetReader(form))
    }.getOrElse(Set.empty)
}

private object HeapExtractor {
  def apply(
      expr: IExpression,
      isCurrentHeap: ProgVarProxy => Boolean
  ): Option[HeapState] = {
    expr match {
      case IEquation(ConstantAsProgVarProxy(h), heap: HeapState) if isCurrentHeap(h) =>
        Some(heap)
      case IEquation(heap: HeapState, ConstantAsProgVarProxy(h)) if isCurrentHeap(h) =>
        Some(heap)
      case IBinFormula(IBinJunctor.And, left, right) =>
        apply(left, isCurrentHeap).orElse(apply(right, isCurrentHeap))
      case IQuantified(IExpression.Quantifier.EX, body) =>
        apply(body, isCurrentHeap)
      case _ => None
    }
  }
}

private object HeapReducer {
  def apply(
      invariantExpression: IExpression,
      heapInfo: HeapInfo,
      values: ValSet = ValSet.empty
  ): IExpression = {
    (new HeapReducer(heapInfo, values)).visit(invariantExpression, List[String]())
  }
}

private class HeapReducer(heapInfo: HeapInfo, values: ValSet)
    extends CollectingVisitor[List[String], IExpression]
    with IdGenerator {

  private object KnownAddress {
    def unapply(term: ITerm): Option[Address] = term match {
      case a: Address => Some(a)
      case _ => values.getVal(term).flatMap(_.variants.collectFirst {
        case a: Address => a
      })
    }
  }

  private object KnownHeap {
    def unapply(term: ITerm): Option[HeapState] = term match {
      case h: HeapState => Some(h)
      case _ => values.getVal(term).flatMap(_.variants.collectFirst {
        case h: HeapState => h
      })
    }
  }

  override def preVisit(
      t: IExpression,
      quantifierIds: List[String]
  ): PreVisitResult = t match {
    case v: IVariableBinder => UniSubArgs(generateId :: quantifierIds)
    case _                  => KeepArg
  }

  override def postVisit(
      t: IExpression,
      quantifierIds: List[String],
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
            Seq(KnownHeap(heap), KnownAddress(addr), obj)
          ) if heapInfo.isWriteFun(writeFun) =>
        heap.write(addr, obj.asInstanceOf[ITerm])
      case IFunApp(
            readFun,
            Seq(KnownHeap(heap), KnownAddress(addr))
          ) if heapInfo.isReadFun(readFun) =>
        heap.storage.getOrElse(addr, t update subres)
      case IFunApp(
            allocFun,
            Seq(KnownHeap(heap), obj)
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
