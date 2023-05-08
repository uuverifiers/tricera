package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext

object EqualitySwapper
    extends IExpressionProcessor
    with ContractConditionTools {
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): IExpression = {
    val precondition = getPrecondition(solution, context)
    val contractCondition = solution(predicate)
    val contractConditionType = getContractConditionType(predicate, context)
    val equalities = contractConditionType match {
      case ContractConditionType.Precondition =>
        EqualityReaderVisitor(precondition)
      case ContractConditionType.Postcondition =>
        val postcondition = getPostcondition(solution, context)
        Equalities.join(
          EqualityReaderVisitor(precondition),
          EqualityReaderVisitor(postcondition)
        )
    }
    val equalitySwapper = new EqualitySwapper(equalitiesToMap(equalities))
    equalitySwapper.swap(contractCondition)
  }

  def equalitiesToMap(equalities: Equalities) = {
    def addMappings(
        map: Map[IExpression, ISortedVariable],
        eqSetWithVar: Set[ITerm]
    ) = {
      val variable = eqSetWithVar.find(_.isInstanceOf[ISortedVariable])
      variable match {
        case Some(v: ISortedVariable) =>
          eqSetWithVar
            .filter(term => term != v)
            .foldLeft(map)((map, term) => map + (term -> v))
      }
    }

    equalities.sets
      .filter(eqSet => eqSet.exists(_.isInstanceOf[ISortedVariable]))
      .foldLeft(Map.empty[IExpression, ISortedVariable])((map, eqSetWithVar) =>
        addMappings(map, eqSetWithVar)
      )
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
