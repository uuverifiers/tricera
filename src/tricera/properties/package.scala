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

import ap.api.SimpleAPI
import ap.parser.IFormula
import tricera.Util.SourceInfo

/**
 * We define the properties (mostly) as defined in SV-COMP
 * [[https://sv-comp.sosy-lab.org/2024/rules.php]].
 */
package object properties {
  sealed trait Property
  sealed trait SubProperty extends Property

  //////////////////////////////////////////////////////////////////////////////
  // Explicit assertions

  /**
   * Unreachability of error function: `reach_error`
   */
  case object Reachability extends Property {
    override def toString : String = "unreach-call"
  }

  case object UserAssertion extends Property {
    override def toString : String = "user-assertion"
  }

  /**
   * Function pre-/post-conditions asserted at function entry and function
   * call sites respectively.
   */
  case class FunctionPrecondition(funName : String,
                                  srcInfo : Option[SourceInfo])
    extends Property {
    override def toString : String = {
      s"precondition of function $funName" +
      (srcInfo match {
        case Some(info) => s" asserted at ${info.line}:${info.col}."
        case None       => ""
      })
    }
  }

  case class FunctionPostcondition(funName : String,
                                   srcInfo : Option[SourceInfo])
    extends Property {
    override def toString : String = {
      s"postcondition of function $funName" +
      (srcInfo match {
        case Some(info) => s" asserted at ${info.line}:${info.col}."
        case None       => ""
      })
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Memory-safety properties

  /**
   * All (reachable) `free` invocations are valid, i.e.,
   *   - no double free,
   *   - no free on non-null, unallocated pointers,
   *   - no free on non-heap variables.
   */
  case object MemValidFree extends SubProperty {
    override def toString : String = "valid-free"
  }

  /**
   * All (reachable) dereferences are valid, i.e.,
   *   - no null/uninitialized pointer dereferences,
   *   - no out-of-bounds array access,
   *   - type safety
   */
  case object MemValidDeref extends SubProperty {
    override def toString : String = "valid-deref"
  }

  /**
   * All allocated memory is tracked, i.e., no memory leaks. In any reachable
   * program path,
   *   - every allocated heap memory associated with a pointer going out of
   *   scope is freed.
   *   - no reassigning a valid heap pointer (pointing to allocating memory),
   *   when only that pointer holds a reference to that memory.
   * @note Programs terminating with allocated memory does not violate this
   *       property, but it violates [[MemValidCleanup]].
   * @note If there are pointers going out of scope due to a `return` from main,
   *       those will violate this property.
   *       See [[https://gitlab.com/sosy-lab/software/cpachecker/-/issues/657]].
   *
   * @todo This property is currently not directly checked by TriCera,
   *       it checks [[MemValidCleanup]] only.
   */
  case object MemValidTrack extends SubProperty {
    override def toString : String = "valid-memtrack"
  }

  /**
   * All allocated memory is deallocated before the program terminates.
   * This property is stronger than [[MemValidTrack]].
   * I.e., if [[MemValidCleanup]] is true, then [[MemValidTrack]] is also true.
   *       If [[MemValidCleanup]] is false, no conclusion can be drawn for
   *       [[MemValidTrack]].
   */
  case object MemValidCleanup extends Property {
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
  // Other properties

  /**
   * In `switch` statements that we never try to jump to a case that does not
   * exist.
   */
  case object SwitchCaseValidJump extends Property
}
