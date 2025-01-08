package tricera

import ap.theories.{Heap}
import ap.parser.IFunction


final case class HeapInfo(val heap: Heap, val heapTermName: String) {
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

  def isCurrentHeap(constant: IFuncParam): Boolean = {
    constant.toString() == heapTermName
  }
}
