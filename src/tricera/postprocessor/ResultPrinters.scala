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

import lazabs.horn.preprocessor.HornPreprocessor
import ap.terfor.preds.Predicate
import ap.parser._
import ap.terfor.ConstantTerm
import lazabs.horn.bottomup.HornClauses.Clause
import hornconcurrency.VerificationLoop
//import lazabs.horn.concurrency.VerificationLoop

object ResultPrinters {

  type HornSolverResult = Either[Option[HornPreprocessor.Solution], VerificationLoop.Counterexample]

  def printSolutionSMT(result: HornSolverResult) = result match {
    case Left(Some(solution)) =>
      import lazabs.horn.global._
      import lazabs.horn.bottomup.HornPredAbs
      import lazabs.ast.ASTree.Parameter
      // TODO: this should probably just use the function for printing
      // models in SMTLineariser. But will change the syntax a bit
      // and require tests to be updated
      // todo: replace args with actual ones from the clauses
      println("\nSolution (SMT-LIB)")
      println("="*80)
      val sortedSol = solution.toArray.sortWith(_._1.name < _._1.name)
      for((pred,sol) <- sortedSol) {
        val cl = HornClause(RelVar(pred.name,
          (0 until pred.arity).zip(HornPredAbs.predArgumentSorts(pred).map(
            lazabs.prover.PrincessWrapper.sort2Type(_))).map(p =>
            Parameter("_" + p._1,p._2)
          ).toList),
          List(Interp(lazabs.prover.PrincessWrapper.formula2Eldarica(sol,
            Map[ap.terfor.ConstantTerm,String]().empty,false))))
        println(lazabs.viewer.HornSMTPrinter.printFull(cl, true))
      }
      println("="*80 + "\n")
    case _ => // Do nothing
  }

  def printSolutionProlog
    (predArgNames: Predicate => Seq[String])
    (result: HornSolverResult)
    : Unit = {
    def clausifySolution(predAndSol  : (Predicate, IFormula),
                         argNames    : Seq[String],
                         newPredName : Option[String] = None) : Clause = {
      val (pred, sol) = predAndSol
      val predArgs = for (predArgName <- argNames) yield
        IConstant(new ConstantTerm(predArgName))
      val constraint  = VariableSubstVisitor.visit(
        sol, (predArgs.toList, 0)).asInstanceOf[IFormula]
      val newPred = newPredName match {
        case Some(newName) => new Predicate(newName, pred.arity)
        case None => pred
      }
      Clause(IAtom(newPred, predArgs), Nil, constraint)
    }
    
    result match {
      case Left(Some(solution)) =>
        println("\nSolution (Prolog)")
        println("="*80)
        val sortedSol = solution.toArray.sortWith(_._1.name < _._1.name)
        for((pred,sol) <- sortedSol) {
          val solClause = clausifySolution(
            (pred, sol), predArgNames(pred), Some(pred.name.stripPrefix("inv_")))
          println(solClause.toPrologString)
        }
        println("="*80 + "\n")
      case _ => // Do Nothing
    }
  }

  def printContracts(contracts: Seq[ACSLLinearisedContract]) = {
    if (!contracts.isEmpty) {
      println("\nInferred ACSL annotations")
      println("=" * 80)
      
      for (contract <- contracts) {
        println(f"/* contracts for ${contract.funcName} */")
        println( "/*@")
        println(f"  requires ${contract.preCondition};")
        println(f"  ensures ${contract.postCondition};")
        println("*/")
        if (!contract.loopInvariants.isEmpty) {
          for (loopInv <- contract.loopInvariants) {
            println(f"/* loop invariant for the loop on line ${loopInv.srcInfo.line} */")
            println( "/*@")
            println(f"  loop invariant ${loopInv.invariant};")
            println("*/")
          }
        }
      }
      println("=" * 80 + "\n")
    }
  }
}
