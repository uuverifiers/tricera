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

  def isHeap(constant: IFuncParam): Boolean = {
    constant.toString() == heapTermName
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
