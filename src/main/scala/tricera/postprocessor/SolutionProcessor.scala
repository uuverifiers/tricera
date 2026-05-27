/**
 * Copyright (c) 2022 Zafer Esen. All rights reserved.
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

import ap.parser._
import IExpression.Predicate

object SolutionProcessor {
  type Solution = Map[Predicate, IFormula]
}

trait SolutionProcessor {
  import SolutionProcessor._

  /**
   * A function to only process process the solutions for the passed list
   * of predicates. This doesn't need to be changed in new solution processors.
   * @param solution       : Solution to process
   * @param predsToProcess : Optionally, a list of predicates whose solutions
   *                         will be processed (default: all)
   * @return               : Returns the processed solution
   */
  def apply(solution       : Solution)
           (predsToProcess : Seq[Predicate] = solution.keys.toSeq): Solution = {
    for ((pred, expr) <- solution) yield
      (pred, (if (predsToProcess contains pred) apply(expr) else expr))
  }

  /**
   * This is the function that should be implemented in new solution processors
   * @param expr : IFormula to process
   * @return     : processed IFormula
   */
  def apply(expr : IFormula) : IFormula
}
