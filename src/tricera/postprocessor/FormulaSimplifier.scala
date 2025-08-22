/**
 * Copyright (c) 2025 Zafer Esen. All rights reserved.
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

import ap.api.SimpleAPI
import ap.parser.{IFormula, SymbolCollector}
import ap.theories.TheoryCollector
import tricera._

object FormulaSimplifier extends ResultProcessor {
  override def applyTo(solution : Solution) : Solution = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(simplify), loopInvariants.map(simplify))
  }
    def simplify(funcInvs: FunctionInvariants) : FunctionInvariants =
      funcInvs match {
    case FunctionInvariants(id, isSrcAnnotated, PreCondition(preInv),
                            PostCondition(postInv), loopInvs) =>
      val newInvs = FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(simplify(preInv)),
        PostCondition(simplify(postInv)),
        loopInvs.map(simplify))
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  def simplify(inv : Invariant) : Invariant = inv match {
    case Invariant(expression, heapInfo, sourceInfo) =>
      Invariant(simplify(expression), heapInfo, sourceInfo)
  }

  def simplify(inv : LoopInvariant) : LoopInvariant = inv match {
    case LoopInvariant(expression, heapInfo, sourceInfo) =>
      LoopInvariant(simplify(expression), heapInfo, sourceInfo)
  }

  def simplify(formula : IFormula): IFormula = (new FormulaSimplifier)(formula)
}

class FormulaSimplifier extends SolutionProcessor {
  override def apply(expr : IFormula) : IFormula =
    SimpleAPI.withProver{ p =>
      p.addConstants(SymbolCollector constantsSorted expr)
      val theoryCollector = new TheoryCollector
      theoryCollector(expr)
      p.addTheories(theoryCollector.theories)
      ACSLExpression.functions.foreach(f => p.addFunction(f))
      ACSLExpression.predicates.foreach(r => p.addRelation(r))
      p.simplify(expr)
    }
}
