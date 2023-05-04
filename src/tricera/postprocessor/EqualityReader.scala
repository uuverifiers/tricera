package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.Heap
import ap.theories.Heap.HeapFunExtractor
import ap.theories.ADT

object Equivalences {
  def apply(term1: ITerm, term2: ITerm): Equivalences = {
    Equivalences(Set(Set(term1, term2)))
  }

  def empty(): Equivalences = {
    Equivalences(Set.empty[Set[ITerm]])
  }

  def join(eqs1: Equivalences, eqs2: Equivalences): Equivalences = {
    (eqs1.equivalenceSet.isEmpty, eqs2.equivalenceSet.isEmpty) match {
      case (true, _) => eqs2
      case (_, true) => eqs1
      case _ =>
        (eqs1.equivalenceSet ++ eqs2.equivalenceSet).foldLeft(
          Equivalences(Set.empty[Set[ITerm]])
        )((cum, cur) => {
          val (hasCommon, rest) = cum.equivalenceSet.partition(_ & cur nonEmpty)
          Equivalences(rest + (cur ++ hasCommon.flatten))
        })
    }
  }
}

case class Equivalences(equivalenceSet: Set[Set[ITerm]]) {
  def addEquality(term1: ITerm, term2: ITerm): Equivalences = {
    val maybeSet1 = getSet(term1)
    val maybeSet2 = getSet(term2)
    (maybeSet1, maybeSet2) match {
      case (Some(set1), Some(set2)) =>
        new Equivalences(equivalenceSet.-(set1).-(set2).+(set1 ++ set2))
      case (Some(set), None) =>
        new Equivalences(equivalenceSet.-(set).+(set.+(term2)))
      case (None, Some(set)) =>
        new Equivalences(equivalenceSet.-(set).+(set.+(term1)))
      case (None, None) =>
        new Equivalences(equivalenceSet.+(Set(term1, term2)))
    }
  }

  def getSet(term: ITerm): Option[Set[ITerm]] = {
    equivalenceSet.find {
      case set: Set[ITerm] if set.contains(term) => true
      case _                                     => false
    }
  }

  override def toString = {
    val setsStrings = equivalenceSet.map { innerSet =>
      innerSet.mkString("{", ", ", "}")
    }
    setsStrings.mkString("", ", \n", "")
  }
}

object EqualityReader extends ContractConditionProcessor {
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): Equivalences = {
    val contractCondition = solution(predicate)
    val contractConditionType = getContractConditionType(predicate, context)
    val acslArgNames = getACSLArgNames(predicate, context)
    EqualityReaderVisitor(contractCondition)
  }

  object EqualityReaderVisitor
      extends CollectingVisitor[Int, Equivalences]
      with ExpressionUtils {

    def apply(contractCondition: IExpression): Equivalences = {
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
        subres: Seq[Equivalences]
    ): Equivalences = {
      def returnDefault = subres.size match {
        case 0 => Equivalences.empty
        case _ => subres.reduce(Equivalences.join(_, _))
      }

      t match {
        case IExpression.EqLit(IFunApp(ADT.CtorId(_, _), Seq(_)), _) => 
            returnDefault

        case e @ IEquation(term1, term2)
            if !ContainsQuantifiedVisitor(e, quantifierDepth) =>
          val shiftedTerm1 = shiftTerm(term1, quantifierDepth)
          val shiftedTerm2 = shiftTerm(term2, quantifierDepth)
          (subres :+ Equivalences(shiftedTerm1, shiftedTerm2)).reduce(
            Equivalences.join(_, _)
          )

        case e @ IIntFormula(IIntRelation.EqZero, term)
            if !ContainsQuantifiedVisitor(e, quantifierDepth) =>
          val shiftedInt = shiftTerm(IIntLit(0), quantifierDepth)
          val shiftedTerm = shiftTerm(term, quantifierDepth)
          (subres :+ Equivalences(shiftedInt, shiftedTerm)).reduce(
            Equivalences.join(_, _)
          )

        case default => returnDefault
      }

    }
  }
}
