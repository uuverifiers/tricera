/**
 * Copyright (c) 2024 Zafer Esen. All rights reserved.
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

/**
 * We define the properties (mostly) as defined in SV-COMP
 * [[https://sv-comp.sosy-lab.org/2024/rules.php]].
 */
package object properties {
  sealed trait Property
  sealed trait PartialProperty extends Property

  //////////////////////////////////////////////////////////////////////////////
  // Explicit assertions

  /**
   * Unreachability of Error Function
   */
  case object Reachability extends Property {
    override def toString : String = "unreach-call"
  }

  //////////////////////////////////////////////////////////////////////////////
  // Memory-safety properties
  // Memory Safety category is composed of multiple disjoint partial properties.

  /**
   * All partial properties related to memory safety. Note that
   * [[MemValidCleanup]] subsumes [[MemValidTrack]], they are not disjoint.
   */
  val memorySafetyProperties : Set[PartialProperty] = Set(
    MemValidFree, MemValidDeref, MemValidTrack, MemValidCleanup)

  /**
   * All (reachable) `free` invocations are valid, i.e.,
   *   - no double free,
   *   - no free on non-null, unallocated pointers,
   *   - no free on non-heap variables.
   *   @todo Our current implementation will consider free on null-pointer as
   *         an error, fix!
   */
  case object MemValidFree extends PartialProperty {
    override def toString : String = "valid-free"
  }

  /**
   * All (reachable) dereferences are valid, i.e.,
   *   - no null/uninitialized pointer dereferences,
   *   - no out-of-bounds array access,
   *   - type safety
   */
  case object MemValidDeref extends PartialProperty {
    override def toString : String = "valid-deref"
  }

  /**
   * All allocated memory is tracked, i.e., no memory leaks. An any reachable
   * program path,
   *   - every allocated heap memory associated with a pointer going out of
   *   scope is freed.
   *   - no reassigning a valid heap pointer (pointing to allocating memory),
   *   when only that pointer holds a reference to that memory.
   * It should be noted that programs terminating with allocated memory does not
   * violate this property (but it violates [[MemValidCleanup]]).
   *
   * @todo We do not ensure memory safety in all cases that pointers can
   *       go out of scope, only function exits, fix!
   * @todo We do not check the latter property at all!
   */
  case object MemValidTrack extends PartialProperty {
    override def toString : String = "valid-memtrack"
  }

  /**
   * All allocated memory is deallocated before the program terminates.
   * This property subsumes [[MemValidTrack]].
   */
  case object MemValidCleanup extends PartialProperty {
    override def toString : String = "valid-memcleanup"
  }

  //////////////////////////////////////////////////////////////////////////////
  // Other SV-COMP properties which TriCera currently does not check for

  case object NoOverflow extends Property {
    override def toString : String = "overflow"
  }

  // For the category 'ConcurrencySafety'
  case object NoDataRace extends Property {
    override def toString : String = "data-race"
  }

  // For the category 'Termination'
  case object Termination extends Property {
    override def toString : String = "termination"
  }

  //////////////////////////////////////////////////////////////////////////////
  // Non-SV-COMP properties

  /**
   * Function pre-/post-conditions asserted at function entry and function
   * call sites respectively.
   */
  case object FunctionPrecondition extends Property
  case object FunctionPostcondition extends Property


  /**
   * In `switch` statements that we never try to jump to a case that does not
   * exist.
   */
  case object SwitchCaseValidJump extends Property
}
