/**
 * Copyright (c) 2025 Scania CV AB. All rights reserved.
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

import tricera.{Result, Solution, CounterExample, Empty, FunctionInvariants}
import tricera.Util.{SourceInfo, printlnDebug}
import ap.parser.IConstant

trait ResultProcessor {
  def apply(result: Result): Result = result match {
    case solution: Solution => applyTo(solution)
    case cex: CounterExample => applyTo(cex)
    case empty: Empty => applyTo(empty)
  } 

  def applyTo(solution: Solution): Solution = {
    solution
  }

  def applyTo(counterExample: CounterExample): CounterExample = {
    counterExample
  }

  def applyTo(empty: Empty): Empty = {
    empty
  }
}

object DebugPrinter {
  def oldAndNew(
    processor: ResultProcessor,
    oldInvs: FunctionInvariants,
    newInvs: FunctionInvariants)
    = {
    printlnDebug(f"----- Applying ${processor} to ${oldInvs.id}.")
    printlnDebug("----- Precondition:")
    printlnDebug(oldInvs.preCondition.invariant.expression.toString)
    printlnDebug("----- New Precondition:")
    printlnDebug(newInvs.preCondition.invariant.expression.toString)
    printlnDebug("----- Postcondition:")
    printlnDebug(oldInvs.postCondition.invariant.expression.toString)
    printlnDebug("----- New Postcondition:")
    printlnDebug(newInvs.postCondition.invariant.expression.toString)
  }
}