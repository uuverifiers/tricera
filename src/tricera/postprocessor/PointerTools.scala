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

package tricera.postprocessor

import tricera.{
    Result, Invariant, InvariantContext, LoopInvariant, PostCondition,
    PreCondition, ProgVarProxy}
import tricera.CounterExample
import tricera.Empty
import tricera.Solution

object PointerTools {
  def inferSafeHeapPointers(result: Result) = SafePointerExtractor(result)
  
  def inferSafeHeapPointers(invContext: InvariantContext) = invContext match {
    case preCond @ PreCondition(invariant) =>
      SafePointerExtractor.getSafePointers(invariant, preCond.isCurrentHeap)
    case postCond @ PostCondition(invariant) =>
      SafePointerExtractor.getSafePointers(invariant, postCond.isCurrentHeap)
    case _ : LoopInvariant => Set[ProgVarProxy]()
  }

  def addPointerPredicatesFrom(sourceResult: Result): Result => Result = sourceResult match {
    case CounterExample(counterExample) => identity
    case Empty() => identity
    case Solution(functionInvariants, _) => (new PointerPropProcessor(functionInvariants)).apply
  }

  def addPointerAssignmentsFrom(sourceResult: Result): Result => Result = sourceResult match {
    case CounterExample(counterExample) => identity
    case Empty() => identity
    case Solution(functionInvariants, _) => (new AssignmentProcessor(functionInvariants)).apply
  }
}
