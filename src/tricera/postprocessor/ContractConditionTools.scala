package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.Heap
import ap.theories.Heap.HeapFunExtractor
import ap.theories.ADT
import tricera.postprocessor.ContractConditionType._

trait ExpressionUtils {
  def iterateUntilFixedPoint(
      expr: IExpression,
      apply: IExpression => IExpression
  ): IExpression = {
    val expressions: Stream[IExpression] = Stream.iterate(expr)(apply)
    expressions
      .zip(expressions.tail)
      .collectFirst { case (a, b) if a == b => a }
      .getOrElse(expr)
  }
}

trait IdGenerator {
  def generateId: String = java.util.UUID.randomUUID.toString
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
  def apply(expr: IExpression): IExpression = {
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
// in depth-first left-first order is replaced by newFormula in
// newExpression, and replacedExpression is the expression that was
// substituted
object ReplaceNthIFormulaVisitor {
  def apply(
      expr: IExpression,
      n: Int,
      replaceByFormula: IFormula
  ): (IExpression, Option[IExpression]) = {
    val replaceFormulaVisitor: ReplaceNthIFormulaVisitor =
      new ReplaceNthIFormulaVisitor(n, replaceByFormula)
    val newFormula = replaceFormulaVisitor.visit(expr, ())
    (newFormula, replaceFormulaVisitor.getReplacedFormula)
  }

  class ReplaceNthIFormulaVisitor(n: Int, replaceByFormula: IFormula)
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
        replaceByFormula
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

// Match types

object Is_O_Sort {
  def unapply(
      expr: IExpression
  ): Option[IExpression] = expr match {
    case IExpression.EqLit(
          IFunApp(
            ADT.CtorId(_, _),
            Seq(arg)
          ),
          _
        ) =>
      Some(arg)

    case _ => None
  }
}

object TheoryOfHeapFunApp {
  def unapply(
      expr: IExpression
  ): Option[(IFunction, Seq[IExpression])] = expr match {
    case IFunApp(
          function @ Heap.HeapFunExtractor(_),
          args
        ) =>
      Some((function, args))

    case _ => None
  }
}

object Var {
  def unapply(
      expr: IExpression
  ): Option[ISortedVariable] = expr match {
    case variable @ ISortedVariable(index, _) =>
      Some(variable)

    case _ => None
  }
}
