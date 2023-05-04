package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.Heap

object ContractConditionType extends Enumeration {
  type ContractConditionType = Value
  val precondition, postcondition = Value
}

import ContractConditionType._

trait ContractConditionProcessor {

  def getContractConditionType(
      predicate: Predicate,
      context: FunctionContext
  ): ContractConditionType = predicate match {
    case context.prePred.pred =>
      ContractConditionType.precondition
    case context.postPred.pred =>
      ContractConditionType.postcondition
  }

  def getACSLArgNames(
      predicate: Predicate,
      context: FunctionContext
  ): Seq[String] = {
    getContractConditionType(predicate, context) match {
      case ContractConditionType.precondition =>
        context.prePredACSLArgNames
      case ContractConditionType.postcondition =>
        context.postPredACSLArgNames
    }
  }
}

trait IExpressionProcessor {
  def apply(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): IExpression = {
    process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
    ): IExpression
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
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): IExpression
}

trait ExpressionUtils {
  def getVarName(
      variableIndex: Int,
      quantifierDepth: Int,
      acslArgNames: Seq[String]
  ): String = {
    acslArgNames(variableIndex - quantifierDepth)
  }

  def isOldHeap(
      variableIndex: Int,
      quantifierDepth: Int,
      acslArgNames: Seq[String]
  ): Boolean = {
    getVarName(variableIndex, quantifierDepth, acslArgNames) == "\\old(@h)"
  }

  def isHeap(
      variableIndex: Int,
      quantifierDepth: Int,
      acslArgNames: Seq[String]
  ): Boolean = {
    getVarName(variableIndex, quantifierDepth, acslArgNames) == "@h"
  }

  def isWriteFun(function: IFunction, heapTheory: Heap): Boolean =
    function == heapTheory.write

  def isReadFun(function: IFunction, heapTheory: Heap): Boolean =
    function == heapTheory.read

  def isGetSortFun(function: IFunction): Boolean =
    function.name.startsWith("get")

  def isO_SortFun(function: IFunction): Boolean = function.name.startsWith("O_")
}

object ContainsQuantifiedVisitor extends CollectingVisitor[Int, Boolean] {
  def apply(expr: IExpression, quantifierDepth: Int): Boolean = {
    ContainsQuantifiedVisitor.visit(expr, quantifierDepth)
  }

  override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult =
    t match {
      case v: ISortedQuantified => UniSubArgs(quantifierDepth + 1)
      case ISortedVariable(index, _) =>
        if (index < quantifierDepth)
          ShortCutResult(true)
        else
          ShortCutResult(false)
      case _ => KeepArg
    }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[Boolean]
  ): Boolean =
    if (subres.isEmpty) false else subres.reduce(_ || _)
}
