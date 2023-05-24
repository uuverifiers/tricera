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
    val noTOHExpr = CleanupVisitor(TheoryOfHeapRemoverVisitor(expr, cci))
    val noTOHOrExplPtrExpr = CleanupVisitor(ExplicitPointerRemover(noTOHExpr, cci))
    val newContractCondition = CleanupVisitor(TrivialEqualityRemover(noTOHOrExplPtrExpr, cci))
    newContractCondition
  }
}

object TheoryOfHeapRemoverVisitor {
  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    (new TheoryOfHeapRemoverVisitor(cci)).visit(expr, 0)
  }
}

class TheoryOfHeapRemoverVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, IExpression] {

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
    extends CollectingVisitor[Unit, Boolean] {

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

object ExplicitPointerRemover extends ContractProcessor {
  def processContractCondition(cci: ContractConditionInfo): IExpression = {
    (new ExplicitPointerRemoverVisitor(cci)).visit(cci.contractCondition, 0)
  }

  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    val newExpr = (new ExplicitPointerRemoverVisitor(cci)).visit(expr, 0)
    CleanupVisitor(newExpr)
  }
}

class ExplicitPointerRemoverVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, IExpression] {

  override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult =
    t match {
      case vb: IVariableBinder =>
        UniSubArgs(quantifierDepth + 1)
      case _ =>
        KeepArg
    }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[IExpression]
  ): IExpression = {
    t update subres match {
    case f: IFormula if ContainsExplicitPointerVisitor(f, quantifierDepth, cci) =>
      IBoolLit(true)
    case _ =>
      t update subres
    }
  }
}

object ContainsExplicitPointerVisitor {
  def apply(expr: IExpression, quantifierDepth: Int, cci: ContractConditionInfo): Boolean = {
    (new ContainsExplicitPointerVisitor(cci))(expr, quantifierDepth)
  }
}

class ContainsExplicitPointerVisitor(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, Boolean] {
  def apply(expr: IExpression, quantifierDepth: Int): Boolean = {
    visit(expr, quantifierDepth)
  }

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = {
    t match {
      case vb: IVariableBinder =>
        UniSubArgs(quantifierDepth + 1)

      case IEquation(v1: ISortedVariable, v2: ISortedVariable)
          if cci.isPointer(v1, quantifierDepth) && cci.isPointer(
            v2,
            quantifierDepth
          ) =>
        ShortCutResult(false)
      case TheoryOfHeapFunApp(_, _) =>
        ShortCutResult(false)
      case IFunApp(fun, _) if cci.isACSLFunction(fun) =>
        ShortCutResult(false)
      case IAtom(pred, _) if cci.isACSLPredicate(pred) =>
        ShortCutResult(false)
      case IBinFormula(IBinJunctor.And, _, _) =>
        ShortCutResult(false)
      case _ =>
        KeepArg
    }
  }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[Boolean]
  ): Boolean = t match {
    case v: ISortedVariable if cci.isPointer(v, quantifierDepth) =>
      true
    case _ =>
      if (subres.isEmpty) false else subres.reduce(_ || _)
  }
}

object TrivialEqualityRemover {
  def apply(expr: IExpression, cci: ContractConditionInfo): IExpression = {
    (new TrivialEqualityRemover(cci)).visit(expr, ())
  }
}

class TrivialEqualityRemover(cci: ContractConditionInfo)
    extends CollectingVisitor[Unit, IExpression] {

  override def postVisit(
      t: IExpression,
      arg: Unit,
      subres: Seq[IExpression]
  ): IExpression = t match {
    case IEquation(left, right) if left == right =>
      IBoolLit(true)
    case _ =>
      t update subres
  }
}
