package tricera.postprocessor

import ap.parser._

case class Address(addressSpaceId: String, counter: Int) extends ITerm {
  override def toString = {
    "Addr" + List("ID" + addressSpaceId.take(4), counter).mkString("(", ",", ")")
  }
}

object HeapState {
  def emptyStorage = Map.empty[Address, ITerm]

  def empty = HeapState("empty", -1, emptyStorage)

  def heapById(id: String) = HeapState(id, -1, Map.empty[Address, ITerm])

}

case class AllocRes(newHeap: HeapState, newAddr: Address) extends ITerm

case class HeapState(
    addressSpaceId: String,
    counter: Int,
    storage: Map[Address, ITerm]
) extends ITerm {
  // addresses <= counter are allocated

  def alloc(obj: ITerm): AllocRes = {
    val allocationAddress = Address(addressSpaceId, counter + 1)
    AllocRes(
      HeapState(addressSpaceId, counter + 1, storage + (allocationAddress -> obj)),
      allocationAddress
    )
  }

  def write(
      addr: Address,
      obj: ITerm
  ): HeapState = {
    if (addressSpaceId == addr.addressSpaceId) {
      writeToAddressSpace(addr, obj)
    } else {
      HeapState(addressSpaceId, counter, HeapState.emptyStorage)
    }
  }

  private def writeToAddressSpace(addr: Address, obj: ITerm): HeapState = {
    if (addr.counter <= counter) {
      val newStorage = this.havocPossibleUnknownAliases(addr).storage + (addr -> obj)
      HeapState(addressSpaceId, counter, newStorage)
    } else {
      this
    }
  }

  def read(
      addr: Address
  ): ITerm = {
    storage.get(addr) match {
      case Some(x) => x
      case None    => this
    }
  }

  private def havocPossibleUnknownAliases(addr: Address): HeapState = {
    val keysToHavoc = storage.keys.filterNot(_.addressSpaceId == addr.addressSpaceId)
    val newStorage = storage -- (keysToHavoc)
    HeapState(addressSpaceId, counter, newStorage)
  }

  override def toString = {
    "Heap" + List("ID" + addressSpaceId.take(4), counter, storage)
      .mkString("(", ",", ")")
  }
}