package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.postprocessor.ContractConditionType._
import ap.types.MonoSortedIFunction
import _root_.tricera.concurrency.ccreader.CCHeapPointer
import _root_.tricera.concurrency.ccreader.CCStackPointer
import _root_.tricera.concurrency.ccreader.CCHeapArrayPointer

case class ContractInfo(
    solution: SolutionProcessor.Solution,
    function: String,
    context: FunctionContext
) {
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

case class ContractConditionInfo(predicate: Predicate, ci: ContractInfo) {
  val prePredicate = ci.prePredicate
  val postPredicate = ci.postPredicate
  val precondition = ci.precondition
  val postcondition = ci.postcondition
  val acslContext = ci.acslContext
  val prePredACSLArgNames = ci.prePredACSLArgNames
  val postPredACSLArgNames = ci.postPredACSLArgNames
  val paramNames = ci.paramNames
  val heapTheory = ci.heapTheory
  val selectors = ci.selectors
  
  val contractConditionType = ci.getContractConditionType(predicate)
  val contractCondition: IExpression = contractConditionType match {
    case ContractConditionType.Precondition =>
      ci.precondition
    case ContractConditionType.Postcondition =>
      ci.postcondition
  }
  val acslArgNames = contractConditionType match {
    case Precondition =>
      ci.prePredACSLArgNames
    case Postcondition =>
      ci.postPredACSLArgNames
  }

  def getVarName(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Option[String] = {
    acslArgNames.lift(variable.index - quantifierDepth)
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

  def isAllocFun(function: IFunction): Boolean = function == heapTheory.alloc

  def isNewHeapFun(function: IFunction): Boolean =
    function == heapTheory.newHeap

  def isNewAddrFun(function: IFunction): Boolean =
    function == heapTheory.newAddr

  def isGetter(function: IFunction): Boolean =
    acslContext.getterSort(function).isDefined

  def isWrapper(function: IFunction): Boolean =
    acslContext.wrapperSort(function).isDefined

  def isStructCtor(fun: MonoSortedIFunction): Boolean = {
    acslContext.getStructMap.get(fun).isDefined
  }

  def isACSLFunction(fun: IFunction): Boolean = {
    ACSLExpression.functions.contains(fun)
  }
  def isACSLPredicate(pred: Predicate): Boolean = {
    ACSLExpression.predicates.contains(pred)
  }

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
    getVarName(variable, quantifierDepth).exists(varName =>
      paramNames.contains(stripOld(varName))
    )
  }

  def isOldVar(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Boolean = {
    getVarName(variable, quantifierDepth).exists(varName =>
      varName.startsWith("\\old")
    )
  }

  def isOldHeap(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Boolean = {
    getVarName(variable, quantifierDepth).exists(_ == "\\old(@h)")
  }

  def isCurrentHeap(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Boolean = {
    getVarName(variable, quantifierDepth).exists(_ == "@h")
  }

  def isPointer(variable: ISortedVariable, quantifierDepth: Int): Boolean = {
    getPureVarName(variable, quantifierDepth) match {
      case Some(varName) =>
        val ccVar = acslContext.getParams
          .find(_.name == varName)
          .orElse(acslContext.getGlobals.find(_.name == varName))

        ccVar.flatMap(ccVariable => Some(ccVariable.typ)) match {
          case Some(_: CCHeapPointer)      => true
          case Some(_: CCStackPointer)     => true
          case Some(_: CCHeapArrayPointer) => true
          case _                     => false
        }
      case None => false
    }
  }

  def getPureVarName(
      variable: ISortedVariable,
      quantifierDepth: Int
  ): Option[String] = {
    getVarName(variable, quantifierDepth) match {
      case Some(varName) => Some(stripOld(varName))
      case None          => None
    }
  }

  def stripOld(input: String): String = {
    val prefix = "\\old("
    val suffix = ")"

    if (input.startsWith(prefix) && input.endsWith(suffix)) {
      input.substring(prefix.length, input.length - suffix.length)
    } else {
      input
    }
  }

  def getGetter(heapTerm: ITerm): Option[IFunction] = {
    heapTerm match {
      case IFunApp(wrapper, _) =>
        acslContext.wrapperSort(wrapper).flatMap(acslContext.sortGetter)
      case _ => None
    }
  }
}

trait ClauseCreator {
  def getClauses(expr: IExpression, cci: ContractConditionInfo): Option[IFormula]
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
