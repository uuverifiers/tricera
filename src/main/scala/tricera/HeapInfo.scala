/**
 * Copyright (c) 2025 Scania CV AB
 *               2026 Zafer Esen. All rights reserved.
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
package tricera

import ap.theories.ADT
import ap.theories.heaps.{ArrayHeap, Heap, NativeHeap}
import ap.parser.IFunction
import tricera.concurrency.ccreader.ArrayPtrOps
import tricera.concurrency.heap.{HeapModel, HeapTheoryModel}


final case class HeapInfo(heap: Heap, heapModel : HeapModel) {
  private val arrayPtrOps : Option[ArrayPtrOps] = heapModel match {
    case m : HeapTheoryModel => Some(m.arrayPtrOps)
    case _ => None
  }

  private val rangeStartSel : Option[IFunction] =
    ADT.Selector.unapply(heap.rangeSize).map {
      case (adt, ctorIndex, _) => adt.selectors(ctorIndex)(0)
    }

  def isRangeNth(function : IFunction) : Boolean = function == heap.rangeNth

  def isRangeSize(function : IFunction) : Boolean = function == heap.rangeSize

  def isRangeStart(function : IFunction) : Boolean =
    rangeStartSel.contains(function)

  def isArrayPtrRange(function : IFunction) : Boolean =
    arrayPtrOps.exists(_.rangeSel == function)

  def isArrayPtrOffset(function : IFunction) : Boolean =
    arrayPtrOps.exists(_.offsetSel == function)

  private def findObjectCtorsAndSels(heap: Heap): Map[IFunction, Option[IFunction]] = {
    heap.userHeapConstructors
      .zip(heap.userHeapSelectors)
      .withFilter({
        case (ctor, sels) => ctor.resSort == heap.ObjectSort
      })
      .map({
        // Object sorts have at most one corresponding selector,
        // with default object having none.
        case (ctor, sels) => (ctor, sels.headOption)
      })
      .toMap
  }

  private val objectCtorToSel = findObjectCtorsAndSels(heap)

  def isHeapSortName(name: String): Boolean =
    name == heap.HeapSort.name

  def isEmptyHeapFun(function: IFunction): Boolean =
    function == heap.emptyHeap

  def isWriteFun(function: IFunction): Boolean =
    function == heap.write

  def isReadFun(function: IFunction): Boolean =
    function == heap.read

  def isAllocFun(function: IFunction): Boolean =
    function == heap.alloc

  def isNewHeapFun(function: IFunction): Boolean =
    function == heap.heapAddrPair_1

  def isNewAddrFun(function: IFunction): Boolean =
    function == heap.heapAddrPair_2

  def isAddrFun(function: IFunction): Boolean =
    function == heap.addr

  private def isHeapTheoryFun(function: IFunction): Boolean =
    Heap.HeapRelatedFunction.unapply(function).contains(heap)

  // The fused allocation functions are private in the heap theories, so
  // they cannot be compared against directly.
  def isAllocHeapFun(function: IFunction): Boolean =
    isHeapTheoryFun(function) &&
      function.arity == 2 && function.name == "allocHeap"

  def isAllocAddrFun(function: IFunction): Boolean =
    isHeapTheoryFun(function) &&
      function.arity == 2 && function.name == "allocAddr"

  val heapSizeFun: Option[IFunction] = heap match {
    case h: NativeHeap => Some(h.heapSize)
    case h: ArrayHeap  => Some(h.heapSize)
    case _             => None
  }

  def isHeap(constant: ProgVarProxy): Boolean = heapModel match {
    case m : HeapTheoryModel =>
      constant.name == m.heapVar.name
    case _ =>
      false
  }

  def isObjCtor(func : IFunction) : Boolean =
    objectCtorToSel.contains(func)

  def isObjSelector(func : IFunction) : Boolean =
    objectCtorToSel.values.exists(_.contains(func))

  def getReadFun: IFunction = heap.read

  def objectCtorToSelector(objectCtor: IFunction): Option[IFunction] =
    objectCtorToSel.get(objectCtor).flatten
}
