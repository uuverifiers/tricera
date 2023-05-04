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

// Indicates whether an IExpression contains a quantifier
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

// Returns the number of free variables minus 1
object MaxIndexVisitor extends CollectingVisitor[Unit, Int] {
  def apply(expr: IExpression): Int = {
    MaxIndexVisitor.visit(expr, ())
  }

  override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
    case v: IVariable => ShortCutResult(v.index)
    case _            => KeepArg
  }

  override def postVisit(t: IExpression, arg: Unit, subres: Seq[Int]): Int =
    if (subres.isEmpty) 0 else subres.max
}

// Returns an IExpression where simplifications related to the literals
// true and false have been made
object CleanupVisitor extends CollectingVisitor[Unit, IExpression] {
  def cleanup(expr: IExpression): IExpression = {
    Rewriter.rewrite(expr, (t) => CleanupVisitor.visit(t, ()))
  }

  override def postVisit(
      t: IExpression,
      arg: Unit,
      subres: Seq[IExpression]
  ): IExpression = t match {
    case IBinFormula(IBinJunctor.And, f1, f2) if (f1 == IBoolLit(true)) => f2
    case IBinFormula(IBinJunctor.And, f1, f2) if (f2 == IBoolLit(true)) => f1
    case IBinFormula(IBinJunctor.And, f1, f2)
        if (f1 == IBoolLit(false) || f2 == IBoolLit(false)) =>
      false
    case IBinFormula(IBinJunctor.Or, f1, f2) if (f1 == IBoolLit(true))  => f1
    case IBinFormula(IBinJunctor.Or, f1, f2) if (f2 == IBoolLit(true))  => f2
    case IBinFormula(IBinJunctor.Or, f1, f2) if (f1 == IBoolLit(false)) => f2
    case IBinFormula(IBinJunctor.Or, f1, f2) if (f2 == IBoolLit(false)) => f1
    case ISortedQuantified(_, _, f) if (f == IBoolLit(true))  => IBoolLit(true)
    case ISortedQuantified(_, _, f) if (f == IBoolLit(false)) => IBoolLit(false)
    case INot(f) if (f == IBoolLit(true))                     => IBoolLit(false)
    case INot(f) if (f == IBoolLit(false))                    => IBoolLit(true)
    case _                                                    => t
  }
}

// Returns a tuple (newExpression, replacedExpression) where n:th IFormula 
// in depth-first left-first order is replaced by a BoolLit(true) in 
// newExpression, and replacedExpression is the expression that was 
// substituted
object ReplaceNthIFormulaVisitor {
  def apply(expr: IExpression, n: Int): (IExpression, Option[IExpression]) = {
    val replaceFormulaVisitor = new ReplaceNthIFormulaVisitor(n)
    val newFormula = replaceFormulaVisitor.visit(expr, ())
    (newFormula, replaceFormulaVisitor.getReplacedFormula)
  }

  class ReplaceNthIFormulaVisitor(n: Int)
      extends CollectingVisitor[Unit, IExpression] {
    private var formulaCount = 0
    private var formula: Option[IExpression] = None

    override def postVisit(
        t: IExpression,
        arg: Unit,
        subres: Seq[IExpression]
    ): IExpression = t match {
      case f: IFormula if formulaCount == n =>
        formula = Some(f)
        formulaCount += 1
        IBoolLit(true)
      case f: IFormula =>
        formulaCount += 1
        t.update(subres)
      case _ =>
        t.update(subres)
    }

    def getReplacedFormula: Option[IExpression] = formula
  }
}

// Returns the number of IFormulas in an IExpression
object IFormulaCounterVisitor extends CollectingVisitor[Unit, Int] {
  def apply(expr: IExpression): Int = {
    IFormulaCounterVisitor.visit(expr, ())
  }

  override def postVisit(t: IExpression, arg: Unit, subres: Seq[Int]): Int =
    t match {
      case f: IFormula => subres.sum + 1
      case _           => subres.sum
    }
}
