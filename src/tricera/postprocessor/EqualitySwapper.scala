package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.postprocessor.ContractConditionType._

object ToVariableForm extends ContractProcessor {
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
    EqualitySwapper.deBrujin(cci.contractCondition, valueSet.toVariableFormMap, cci)
  }
}

object ToExplicitForm {
  def deBrujin(expr: IExpression, valueSet: ValSet, cci: ContractConditionInfo) = {
    EqualitySwapper.deBrujin(expr, valueSet.toExplicitFormMap, cci)
  } 

  def invariant(expr: IExpression, valueSet: ValSet, cci: ContractConditionInfo) = {
    EqualitySwapper.invariant(expr, valueSet.toExplicitFormMap, cci)
  } 
}

object EqualitySwapper {
  def deBrujin(expr: IExpression, swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo) = {
    (new EqualitySwapper(swapMap, cci))(expr)
  }

  def invariant(expr: IExpression, swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo) = {
    (new InvariantEqualitySwapper(swapMap, cci))(expr)
  }
}

class EqualitySwapper(swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo)
    extends CollectingVisitor[Int, IExpression] 
    with ExpressionUtils {

  // swaps every expression except equalities but including the @h expression
  def apply(contractCondition: IExpression): IExpression = {
    def rewriter(expr: IExpression): IExpression = {
      visit(expr, 0)
    }
    iterateUntilFixedPoint(contractCondition, rewriter)
  }

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case IEquation(v: ISortedVariable, term) if !cci.isCurrentHeap(v, quantifierDepth) =>
      ShortCutResult(t)
    case IEquation(term, v: ISortedVariable) if !cci.isCurrentHeap(v, quantifierDepth) =>
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
    case h: ISortedVariable if cci.isCurrentHeap(h, quantifierDepth) =>
      t update subres 
    case term: ITerm =>
      val res = t update subres
      val shiftedTerm =
        VariableShiftVisitor(term, quantifierDepth, -quantifierDepth)
      swapMap.get(shiftedTerm) match {
        case Some(variable) =>
          val newVariable =
            VariableShiftVisitor(variable, 0, quantifierDepth)
          newVariable
        case None =>
          res
      }
    case default => t update subres
  }
}

class InvariantEqualitySwapper(swapMap: Map[IExpression, ITerm], cci: ContractConditionInfo) extends EqualitySwapper(swapMap, cci) {

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case IEquation(v: ISortedVariable, term) if !cci.isCurrentHeap(v, quantifierDepth) =>
      ShortCutResult(t)
    case IEquation(term, v: ISortedVariable) if !cci.isCurrentHeap(v, quantifierDepth) =>
      ShortCutResult(t)
    case IIntFormula(IIntRelation.EqZero, term) =>
      ShortCutResult(t)
    case _ =>
      KeepArg
  }
}
