package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.SimpleAPI.ProverStatus
import ap.SimpleAPI.TimeoutException
import ap.theories._
import ap.SimpleAPI

object PostconditionSimplifier extends ContractProcessor {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    cci.contractConditionType match {
      case ContractConditionType.Precondition =>
        cci.contractCondition
      case ContractConditionType.Postcondition =>
        apply(cci.precondition, cci.postcondition)
    }
  }

  def apply(precond: IExpression, postcond: IExpression): IExpression = {
    val precondition = precond.asInstanceOf[IFormula]
    var postcondition = postcond.asInstanceOf[IFormula]

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
      postcondition = CleanupVisitor(postcondition).asInstanceOf[IFormula]
    }
    attemptReplacingIFormulasBy(IBoolLit(true))
    attemptReplacingIFormulasBy(IBoolLit(false))
    postcondition
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
