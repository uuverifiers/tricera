package tricera

import ap.theories.{Heap}


final case class HeapInfo(val heap: Heap) {
  val heapTermName = "@h"
  
  def isCurrentHeap(constant: IFuncParam): Boolean = {
    constant.toString() == heapTermName
  }
}
