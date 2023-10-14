/**
 * Copyright (c) 2011-2019 Oskar Soederberg. All rights reserved.
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

 /* HeapRepresentation.scala
 *  
 * Definitions related to a "heap simulator" which can translate theory 
 * of heap expressions to a map containing relevant information. This is
 * used by PointerPropProcessor.
 */

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