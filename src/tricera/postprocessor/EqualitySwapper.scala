package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.postprocessor.ContractConditionType._

object EqualitySwapper extends ContractProcessor {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    val valueSet = cci.contractConditionType match {
      case Precondition =>
        ValSetReader.deBrujin(cci.precondition)
      case Postcondition =>
        ValSet.merge(
          ValSetReader.deBrujin(cci.precondition),
          ValSetReader.deBrujin(cci.postcondition)
        )
    }
    EqualitySwapper(cci.contractCondition, equalitiesToMap(valueSet))
  }

  def equalitiesToMap(valueSet: ValSet): Map[IExpression, ISortedVariable] = {
    valueSet.vals
      .collect {
        case value if value.getVariableForm.isDefined =>
          val variable = value.getVariableForm.get.asInstanceOf[ISortedVariable]
          value.variants
            .filterNot(_ == variable)
            .map(_ -> variable)
      }
      .flatten
      .toMap
  }

  object EqualitySwapper {
    def apply(expr: IExpression, swapMap: Map[IExpression, ISortedVariable]) = {
      (new EqualitySwapper(swapMap)).swap(expr)
    }
  }

  class EqualitySwapper(swapMap: Map[IExpression, ISortedVariable])
      extends CollectingVisitor[Int, IExpression] {
    def swap(contractCondition: IExpression): IExpression = {
      visit(contractCondition, 0)
    }

    override def preVisit(
        t: IExpression,
        quantifierDepth: Int
    ): PreVisitResult = t match {
      case IEquation(v: IVariable, term) =>
        ShortCutResult(t)
      case IEquation(term, v: IVariable) =>
        ShortCutResult(t)
      case IIntFormula(IIntRelation.EqZero, term) =>
        ShortCutResult(t)
      case vb: IVariableBinder =>
        UniSubArgs(quantifierDepth + 1)
      case _ =>
        KeepArg
    }

    override def postVisit(
        t: IExpression,
        quantifierDepth: Int,
        subres: Seq[IExpression]
    ): IExpression = t match {
      case term: ITerm =>
        val res = t update subres
        val shiftedTerm =
          VariableShiftVisitor(term, quantifierDepth, -quantifierDepth)
        swapMap.get(shiftedTerm) match {
          case Some(variable) =>
            val newVariable =
              VariableShiftVisitor(variable, 0, quantifierDepth)
            println("replacing " + term + " by " + newVariable)
            newVariable
          case None =>
            res
        }
      case default => t update subres
    }
  }
}
