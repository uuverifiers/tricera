package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.Heap
import ap.theories.Heap.HeapFunExtractor
import ap.theories.ADT

object Equalities {
  def apply(term1: ITerm, term2: ITerm): Equalities = {
    Equalities(Set(Set(term1, term2)))
  }

  def empty(): Equalities = {
    Equalities(Set.empty[Set[ITerm]])
  }

  def join(eqs1: Equalities, eqs2: Equalities): Equalities = {
    (eqs1.sets.isEmpty, eqs2.sets.isEmpty) match {
      case (true, _) => eqs2
      case (_, true) => eqs1
      case _ =>
        (eqs1.sets ++ eqs2.sets).foldLeft(
          Equalities(Set.empty[Set[ITerm]])
        )((cum, cur) => {
          val (hasCommon, rest) = cum.sets.partition(_ & cur nonEmpty)
          Equalities(rest + (cur ++ hasCommon.flatten))
        })
    }
  }
}

case class Equalities(sets: Set[Set[ITerm]]) {
  def addEquality(term1: ITerm, term2: ITerm): Equalities = {
    val maybeSet1 = getSet(term1)
    val maybeSet2 = getSet(term2)
    (maybeSet1, maybeSet2) match {
      case (Some(set1), Some(set2)) =>
        new Equalities(sets.-(set1).-(set2).+(set1 ++ set2))
      case (Some(set), None) =>
        new Equalities(sets.-(set).+(set.+(term2)))
      case (None, Some(set)) =>
        new Equalities(sets.-(set).+(set.+(term1)))
      case (None, None) =>
        new Equalities(sets.+(Set(term1, term2)))
    }
  }

  def getSet(term: ITerm): Option[Set[ITerm]] = {
    sets.find {
      case set: Set[ITerm] if set.contains(term) => true
      case _                                     => false
    }
  }

  override def toString = {
    val setsStrings = sets.map { innerSet =>
      innerSet.mkString("{", ", ", "}")
    }
    setsStrings.mkString("", ", \n", "")
  }
}

object EqualityReader extends ContractConditionTools {
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): Equalities = {
    val contractCondition = solution(predicate)
    val contractConditionType = getContractConditionType(predicate, context)
    val acslArgNames = getACSLArgNames(predicate, context)
    EqualityReaderVisitor(contractCondition)
  }
}

object EqualityReaderVisitor
    extends CollectingVisitor[Int, Equalities]
    with ExpressionUtils {

  def apply(contractCondition: IExpression): Equalities = {
    visit(contractCondition, 0)
  }

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case v: IVariableBinder => UniSubArgs(quantifierDepth + 1)
    case _                  => KeepArg
  }

  private def shiftTerm(term: ITerm, quantifierDepth: Int) =
    VariableShiftVisitor(term, quantifierDepth, -quantifierDepth)

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[Equalities]
  ): Equalities = {
    def returnDefault = subres.size match {
      case 0 => Equalities.empty
      case _ => subres.reduce(Equalities.join(_, _))
    }

    t match {
      case IExpression.EqLit(IFunApp(ADT.CtorId(_, _), Seq(_)), _) =>
        returnDefault

      case e @ IEquation(term1, term2)
          if !ContainsQuantifiedVisitor(e, quantifierDepth) =>
        val shiftedTerm1 = shiftTerm(term1, quantifierDepth)
        val shiftedTerm2 = shiftTerm(term2, quantifierDepth)
        (subres :+ Equalities(shiftedTerm1, shiftedTerm2)).reduce(
          Equalities.join(_, _)
        )

      case e @ IIntFormula(IIntRelation.EqZero, term)
          if !ContainsQuantifiedVisitor(e, quantifierDepth) =>
        val shiftedInt = shiftTerm(IIntLit(0), quantifierDepth)
        val shiftedTerm = shiftTerm(term, quantifierDepth)
        (subres :+ Equalities(shiftedInt, shiftedTerm)).reduce(
          Equalities.join(_, _)
        )

      case default => returnDefault
    }

  }
}
