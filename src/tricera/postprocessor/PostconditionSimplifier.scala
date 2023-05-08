package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.SimpleAPI.ProverStatus
import ap.SimpleAPI.TimeoutException
import ap.theories._
import ap.SimpleAPI

object PostconditionSimplifier
    extends IExpressionProcessor
    with ContractConditionTools {
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): IExpression = {
    getContractConditionType(predicate, context) match {
      case ContractConditionType.Postcondition =>
        apply(solution, context)
    }
  }

  def apply(
      solution: SolutionProcessor.Solution,
      context: FunctionContext
  ): IExpression = {
    val precondition = solution(context.prePred.pred).asInstanceOf[IFormula]
    var postcondition = solution(context.postPred.pred).asInstanceOf[IFormula]
    var i = 0
    var cont = true
    while (cont) {
      ReplaceNthIFormulaVisitor(postcondition, i) match {
        case (newPostcondition, Some(replacedFormula)) =>
          isEquivalentPostcondition(
            precondition,
            postcondition,
            newPostcondition.asInstanceOf[IFormula]
          ) match {
            case true =>
              postcondition = newPostcondition.asInstanceOf[IFormula]
              val removedIFormulas = IFormulaCounterVisitor(replacedFormula) - 1
              i = i + 1 - removedIFormulas
            case false =>
              i = i + 1
          }
        case (_, None) =>
          cont = false
      }
    }
    CleanupVisitor.cleanup(postcondition)
  }

  def replaceVarsWithConstants(p: SimpleAPI, formula: IFormula): IFormula = {
    val maxIndex = MaxIndexVisitor(formula)
    val constants = p.createConstants("c", 0 to maxIndex).toList
    VariableSubstVisitor(formula.asInstanceOf[IFormula], (constants, 0))
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
      val constFormula = replaceVarsWithConstants(p, formula)
      collectAndAddTheories(p, formula)

      p.??(constFormula)

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
