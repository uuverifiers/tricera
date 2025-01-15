/**
 * Copyright (c) 2023 Oskar Soederberg. All rights reserved.
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

/* PostconditionSimplifier.scala
 *   
 * See PostconditionSimplifier in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 *
 * In this contract processor, attempts are made to simplify the postcondition by 
 * using the information in the precondition. This is done as the simplified 
 * postcondition may contain more clauses that are directly expressible in ACSL. 
 * The precondition is left unchanged.
 */

package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.{Solution, FunctionInvariants, Invariant}
import ap.SimpleAPI.ProverStatus
import ap.SimpleAPI.TimeoutException
import ap.theories._
import ap.SimpleAPI

import scala.collection.mutable.{Set, HashSet}

object PostconditionSimplifier extends ResultProcessor {

  override def applyTo(solution: Solution) = solution match {
    case Solution(functionInvariants, heapInfo) =>
      Solution(functionInvariants.map(simplifyPostCondition(_)), heapInfo)
  }

  private def simplifyPostCondition(funcInvs: FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(id, preCondition, postCondition, loopInvariants) => 
      val newInvs = FunctionInvariants(
        id,
        preCondition,
        Invariant(
          simplify(preCondition.expression, postCondition.expression),
          postCondition.sourceInfo),
        loopInvariants)
      DebugPrinter.oldAndNew(PostconditionSimplifier, funcInvs, newInvs)
      newInvs
  }

  private def simplify(precondition: IFormula, postcond: IFormula): IFormula = {
    var postcondition = postcond

    def attemptReplacingIFormulasBy(replaceByFormula: IFormula) = {
      var i = 0
      var cont = true
      while (cont) {
        ReplaceNthIFormulaVisitor(postcondition, i, replaceByFormula) match {
          case (newPostcondition, Some(replacedFormula)) =>
            isEquivalentPostcondition(
              precondition,
              postcondition,
              newPostcondition.asInstanceOf[IFormula]
            ) match {
              case true =>
                postcondition = newPostcondition.asInstanceOf[IFormula]
                val removedIFormulas =
                  IFormulaCounterVisitor(replacedFormula) - 1
                i = i + 1 - removedIFormulas
              case false =>
                i = i + 1
            }
          case (_, None) =>
            cont = false
        }
      }
      // Note: Cleanup rules for false literals are not yet implemented in CleanupVisitor
      // SSSOWO: Actually I think they are. Please check!
      postcondition = CleanupVisitor(postcondition).asInstanceOf[IFormula]
    }
    attemptReplacingIFormulasBy(IBoolLit(true))
    attemptReplacingIFormulasBy(IBoolLit(false))
    postcondition
  }

  def collectAndAddTheories(p: SimpleAPI, formula: IFormula) = {
    val theories: Seq[Theory] = {
      val coll = new TheoryCollector
      coll(formula)
      coll.theories
    }
    p.addTheories(theories)
  }

  def isEquivalentPostcondition(
      precondition: IFormula,
      postcondition: IFormula,
      simplifiedPostcondition: IFormula
  ): Boolean = {
    SimpleAPI.withProver { p =>
      val formula =
        precondition
          .==>(postcondition.<=>(simplifiedPostcondition))
          .asInstanceOf[IFormula]
      p.addConstants(CollectConstants(formula))
      collectAndAddTheories(p, formula)

      p.??(formula)

      val result =
        try
          p.withTimeout(100) {
            p.???
          }
        catch {
          case x: SimpleAPI.SimpleAPIException if x == TimeoutException =>
            None
        }

      result match {
        case ProverStatus.Valid =>
          true
        case _ =>
          false
      }
    }
  }
}

private object CollectConstants {
  def apply(formula: IFormula) = {
    val constants = new HashSet[ITerm]()
    (new CollectConstantsVisitor()).visit(formula, constants)
    constants
  }
}

private class CollectConstantsVisitor extends CollectingVisitor[Set[ITerm], Unit] {
  override def postVisit(t: IExpression, constants: Set[ITerm], subres: Seq[Unit]): Unit = t match {
    case c: IConstant =>
      constants.add(c)
    case _ =>
  }
}