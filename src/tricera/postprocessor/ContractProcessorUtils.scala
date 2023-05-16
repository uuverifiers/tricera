package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.postprocessor.ContractConditionType._
import ap.types.MonoSortedIFunction

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
  val paramNames = acslContext.getParams.map(x => x.name)
  val heapTheory = acslContext.getHeap
  val selectors = acslContext.getStructMap.values
    .map((struct) => struct.sels.map(_._1))
    .toSet
    .flatten

  // vals unique for the contract condition
  val contractConditionType = contractInfo.getContractConditionType(predicate)
  val contractCondition: IExpression = contractConditionType match {
    case ContractConditionType.Precondition =>
      precondition
    case ContractConditionType.Postcondition =>
      postcondition
  }
  val acslArgNames = contractConditionType match {
    case Precondition =>
      prePredACSLArgNames
    case Postcondition =>
      postPredACSLArgNames
  }

  def getVarName(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): String = {
    acslArgNames(variable.index - quantifierDepth)
  }

  def isSelector(
      function: IFunction
  ): Boolean = {
    function match {
      case monoFun: MonoSortedIFunction =>
        selectors.contains(monoFun)
      case _: IFunction => false
    }
  }

  def isWriteFun(function: IFunction): Boolean = function == heapTheory.write

  def isReadFun(function: IFunction): Boolean = function == heapTheory.read

  def isGetter(function: IFunction): Boolean =
    acslContext.getterSort(function).isDefined

  def isWrapper(function: IFunction): Boolean =
    acslContext.wrapperSort(function).isDefined

  def isPrecondition: Boolean = {
    contractConditionType == Precondition
  }

  def isPostcondition: Boolean = {
    contractConditionType == Postcondition
  }

  def isParam(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Boolean = {
    val varName = stripOld(getVarName(variable, quantifierDepth))
    paramNames.contains(varName)
  }

  def isOldVar(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Boolean = {
    val varName = getVarName(variable, quantifierDepth)
    varName.startsWith("\\old")
  }

  def isOldHeap(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Boolean = {
    getVarName(variable, quantifierDepth) == "\\old(@h)"
  }

  def isHeap(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Boolean = {
    getVarName(variable, quantifierDepth) == "@h"
  }

  def stripOld(input: String): String = {
    val prefix = "\\old("
    val suffix = ")"

    if (input.startsWith(prefix) && input.endsWith(suffix)) {
      input.substring(prefix.length, input.length - suffix.length)
    } else if (
      !input.contains("(") && !input.contains(")") && !input.contains("\\")
    ) {
      input
    } else {
      throw new IllegalArgumentException(s"Invalid input: $input")
    }
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
    (
      processContractCondition(preconditionInfo),
      processContractCondition(postconditionInfo)
    ): (
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
