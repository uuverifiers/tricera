/**
 * Copyright (c) 2025 Ola Wingbrant. All rights reserved.
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

import ap.theories.{Heap}
import ap.parser.{IFunction, ITerm, IFunApp}


final case class HeapInfo(val heap: Heap, val heapTermName: String) {
  private def findObjectCtorsAndSels(heap: Heap): Map[IFunction, Option[IFunction]] = {
    heap.userADTCtors
      .zip(heap.userADTSels)
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
    function == heap.newHeap

  def isNewAddrFun(function: IFunction): Boolean =
    function == heap.newAddr

  def isHeap(constant: ProgVarProxy): Boolean = {
    constant.name == heapTermName
  }

  def isObjCtor(func: IFunction): Boolean = {
    objectCtorToSel.get(func).isDefined
  }

  def isObjSelector(func: IFunction): Boolean = {
    objectCtorToSel.values.exists(
      value => value.map(v => v == func).getOrElse(false)) 
  }


  def getReadFun: IFunction = heap.read

  def objectCtorToSelector(objectCtor: IFunction): Option[IFunction] = {
    objectCtorToSel.get(objectCtor).flatten
  }
}
