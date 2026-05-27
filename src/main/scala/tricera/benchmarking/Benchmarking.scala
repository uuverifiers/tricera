/**
 * Copyright (c) 2021-2024 Zafer Esen. All rights reserved.
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

package tricera.benchmarking

import tricera.properties

object Benchmarking {
  // Execution Results
  sealed trait ExecutionError
  sealed abstract class ExecutionResult {
    def toString : String
  }
  case class ParseError (e : String) extends ExecutionResult with ExecutionError {
    override def toString : String =
      "Parse Error: " + e
  }
  case class TranslationError (e : String) extends ExecutionResult with ExecutionError {
    override def toString : String =
      "Horn Translation Error: " + e
  }
  case object OutOfMemory extends ExecutionResult with ExecutionError  {
    override def toString : String =
      "Out of Memory"
  }
  case object StackOverflow extends ExecutionResult with ExecutionError  {
    override def toString : String =
      "Stack Overflow"
  }
  case class OtherError (e : String) extends ExecutionResult with ExecutionError {
    override def toString : String =
      "Other Error: " + e
  }
  case object Timeout extends ExecutionResult with ExecutionError {
    override def toString : String =
      "TIMEOUT"
  }
  case object Safe extends ExecutionResult {
    override def toString : String =
      "SAFE"
  }
  case object Unsafe extends ExecutionResult {
    override def toString : String =
      "UNSAFE"
  }
  case class Unknown(reason : String = "") extends ExecutionResult {
    override def toString: String =
      "UNKNOWN" + (if(reason.nonEmpty) s" ($reason)" else "")
  }
  case object DidNotExecute extends ExecutionResult {
    override def toString : String =
      //"DID NOT EXECUTE"
    ""
  }

  // returned by Main
  case class ExecutionSummary (
    executionResult : ExecutionResult,
    // if a supported SV-COMP track is provided, returns a list of these tracks
    // and whether the execution result matched the expected verdict or not
    propertyResult  : Map[properties.Property, Boolean] = Map(),
    modelledHeap    : Boolean = false, // true if the bm contained heap operations
    elapsedTime     : Double = 0,
    preprocessTime  : Double = 0
                              ) {
    override def toString: String = {
      "Result   : " + executionResult + "\n" +
      "Duration : " + elapsedTime + " s"
    }
  }

  class Timer {
    private var stopped = true
    private var startTime : Double = System.nanoTime()
    private var stopDuration  : Double = 0

    def pause() { stopped = true; stopDuration = System.nanoTime() - startTime }
    def stop()  { stopped = true; stopDuration = System.nanoTime() - startTime }
    def start() { stopped = false; startTime = System.nanoTime() }

    def s  : Double = ns / 1e9d
    def ms : Double = ns / 1e6d
    def us : Double = ns / 1e3d
    def ns : Double =
      if (stopped) stopDuration else System.nanoTime() - startTime
  }

}
