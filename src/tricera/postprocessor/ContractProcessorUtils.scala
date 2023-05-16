package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.postprocessor.ContractConditionType._

case class ContractInfo(
    solution: SolutionProcessor.Solution,
    function: String,
    context: FunctionContext
) {
  def getContractConditionType(
      predicate: Predicate
  ): ContractConditionType = predicate match {
    case context.prePred.pred =>
      ContractConditionType.Precondition
    case context.postPred.pred =>
      ContractConditionType.Postcondition
  }

  def toContractConditionInfo(predicate: Predicate): ContractConditionInfo = {
    ContractConditionInfo(predicate, this)
  }
}

case class ContractConditionInfo(
    predicate: Predicate,
    contractInfo: ContractInfo
) {
  val solution = contractInfo.solution
  val context = contractInfo.context
  val prePredicate = context.prePred.pred
  val postPredicate = context.postPred.pred
  val precondition = solution(prePredicate)
  val postcondition = solution(postPredicate)
  val acslContext = context.acslContext
  val prePredACSLArgNames = context.prePredACSLArgNames
  val postPredACSLArgNames = context.postPredACSLArgNames

  val contractConditionType = contractInfo.getContractConditionType(predicate)
  val acslArgNames = contractConditionType match {
    case Precondition =>
      prePredACSLArgNames
    case Postcondition =>
      postPredACSLArgNames
  }

  val contractCondition: IExpression = contractConditionType match {
    case ContractConditionType.Precondition =>
      precondition
    case ContractConditionType.Postcondition =>
      postcondition
  }
}

trait ContractProcessor {
  def apply(
      solution: SolutionProcessor.Solution,
      function: String,
      context: FunctionContext
  ): (IExpression, IExpression) = {
    val contractInfo = ContractInfo(solution, function, context)
    val preconditionInfo =
      contractInfo.toContractConditionInfo(context.prePred.pred)
    val postconditionInfo =
      contractInfo.toContractConditionInfo(context.postPred.pred)
    (processContractCondition(preconditionInfo), processContractCondition(postconditionInfo)): (
        IExpression,
        IExpression
    )
  }

  /** This is the function that should be implemented in new
    * ContractConditionProcessors
    * @param solution
    *   : All predicates in solution
    * @param predicate
    *   : Predicate to process
    * @param function
    *   : function name
    * @param context
    *   : function context
    * @return
    *   : processed IExpression
    */
  def processContractCondition(
      contractConditionInfo: ContractConditionInfo
  ): IExpression
}
