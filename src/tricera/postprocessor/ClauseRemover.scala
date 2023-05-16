package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ContractConditionType._

object ClauseRemover extends ContractProcessor {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    apply(cci.contractCondition, cci)
  }

  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    val newContractCondition = TheoryOfHeapRemoverVisitor(expr, cci)
    // add additional clause remover visitors here (explicit pointers, etc.)
    CleanupVisitor(newContractCondition)
  }
}

object TheoryOfHeapRemoverVisitor {
  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    (new TheoryOfHeapRemoverVisitor(cci)).visit(expr, 0)
  }
}

class TheoryOfHeapRemoverVisitor(cci: ContractConditionInfo) extends CollectingVisitor[Int, IExpression] {

  override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult =
    t match {
      case default =>
        KeepArg
    }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[IExpression]
  ): IExpression = t match {
    case IBinFormula(IBinJunctor.And, _, _) =>
      val f1 = subres(0)
      val f2 = subres(1)
      (ContainsTOHVisitor(f1, cci), ContainsTOHVisitor(f2, cci)) match {
        case (false, false) =>
          t update subres
        case (true, false) =>
          f2
        case (false, true) =>
          f1
        case (true, true) =>
          IBoolLit(true)
      }
    case q @ ISortedQuantified(_, _, formula) =>
      q update subres
    case default => t update subres
  }
}

object ContainsTOHVisitor {
  def apply(expr: IExpression, cci: ContractConditionInfo): Boolean = {
    (new ContainsTOHVisitor(cci))(expr)
  }
}

class ContainsTOHVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Unit, Boolean]
    with ExpressionUtils {
  import ap.theories.Heap

  def apply(expr: IExpression): Boolean = {
    visit(expr, ())
  }

  override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
    case TheoryOfHeapFunApp(_, _) =>
      ShortCutResult(true)
    case IFunApp(fun, args) if (cci.isGetter(fun) || cci.isWrapper(fun)) =>
      ShortCutResult(true)
    case _ =>
      KeepArg
  }

  override def postVisit(
      t: IExpression,
      arg: Unit,
      subres: Seq[Boolean]
  ): Boolean =
    if (subres.isEmpty) false else subres.reduce(_ || _)
}
