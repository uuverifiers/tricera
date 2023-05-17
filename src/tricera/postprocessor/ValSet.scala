package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.ADT

object Val {
  def apply(term1: ITerm, term2: ITerm): Val = {
    Val(Set(term1, term2))
  }

  def merge(vals: Set[Val]): Val = {
    vals.reduce((val1, val2) => (val1 | val2))
  }
}
case class Val(variants: Set[ITerm]) {
  def getExplicitForm: Option[ITerm] = variants find {
    case a: Address         => false
    case v: ISortedVariable => false
    case _                  => true
  }

  def getAddrForm: Option[ITerm] = variants find {
    case a: Address => true
    case _          => false
  }

  def getVariableForm: Option[ITerm] = variants find {
    case v: ISortedVariable => true
    case _                  => false
  }

  def +(term: ITerm): Val = {
    Val(variants + term)
  }

  def +(v: Val): Val = {
    Val.merge(Set(this, v))
  }

  def &(v: Val): Val = {
    Val(variants & v.variants)
  }

  def |(v: Val): Val = {
    Val(variants | v.variants)
  }

  def nonEmpty: Boolean = {
    variants.nonEmpty
  }
}

object ValSet {

  def apply(term1: ITerm, term2: ITerm): ValSet = {
    ValSet(Set(Val(term1, term2)))
  }

  def empty(): ValSet = {
    ValSet(Set.empty[Val])
  }

  def merge(vs1: ValSet, vs2: ValSet): ValSet = {
    (vs1.isEmpty, vs2.isEmpty) match {
      case (true, _) => vs2
      case (_, true) => vs1
      case _ =>
        (vs1.vals ++ vs2.vals).foldLeft(
          ValSet.empty
        )((vs, v) => {
          val (equalVals, rest) = vs.vals.partition(_ & v nonEmpty)
          val newVal: Val = if (equalVals.nonEmpty) {
            Val.merge(equalVals + v)
          } else {
            v
          }
          ValSet(rest + (newVal))
        })
    }
  }
}

case class ValSet(vals: Set[Val]) {

  def addEquality(term1: ITerm, term2: ITerm): ValSet = {
    val maybeVal1 = getVal(term1)
    val maybeVal2 = getVal(term2)
    (maybeVal1, maybeVal2) match {
      case (Some(val1), Some(val2)) =>
        ValSet(vals.-(val1).-(val2).+(val1 + val2))
      case (Some(v), None) =>
        ValSet(vals.-(v).+(v.+(term2)))
      case (None, Some(v)) =>
        ValSet(vals.-(v).+(v.+(term1)))
      case (None, None) =>
        ValSet(vals.+(Val(term1, term2)))
    }
  }

  def isEmpty = vals.isEmpty

  def getVal(term: ITerm): Option[Val] = {
    vals.find {
      case v: Val if v.variants.contains(term) => true
      case _                                   => false
    }
  }

  def getExplicitForm(term: ITerm): Option[ITerm] = {
    getVal(term) match {
      case Some(v) => v.getExplicitForm
      case None    => None
    }
  }

  def getVariableForm(term: ITerm): Option[ITerm] = {
    getVal(term) match {
      case Some(v) => v.getVariableForm
      case None    => None
    }
  }

  def toVariableFormMap: Map[IExpression, ISortedVariable] = {
    vals
      .collect {
        case value if value.getVariableForm.isDefined =>
          val variable = value.getVariableForm.get.asInstanceOf[ISortedVariable]
          value.variants
            .filterNot(_ == variable)
            .map(_ -> variable)
      }
      .flatten
      .toMap
  }

  def toExplicitFormMap: Map[IExpression, ITerm] = {
    vals
      .collect {
        case value if value.getExplicitForm.isDefined =>
          val variable = value.getExplicitForm.get
          value.variants
            .filterNot(_ == variable)
            .map(_ -> variable)
      }
      .flatten
      .toMap
  }

  def merge(eqs: ValSet): ValSet = {
    ValSet.merge(this, eqs)
  }

  override def toString = {
    val setsStrings = vals.map { v =>
      v.variants.mkString("{", " :: ", "}")
    }
    setsStrings.mkString("", ", \n", "")
  }
}

object ValSetReader {
  // NOTE: expressions must be invariant and unique (not de Bruijn indexed)
  def invariant(contractCondition: IExpression): ValSet = {
    InvariantReader.visit(contractCondition, ())
  }

  def deBrujin(contractCondition: IExpression): ValSet = {
    DeBrujinReader.visit(contractCondition, 0)
  }

  object InvariantReader
      extends CollectingVisitor[Unit, ValSet]
      with ExpressionUtils {

    override def postVisit(
        t: IExpression,
        arg: Unit,
        subres: Seq[ValSet]
    ): ValSet = {
      def returnDefault = subres.size match {
        case 0 => ValSet.empty
        case _ => subres.reduce(ValSet.merge(_, _))
      }

      t match {
        // skip is_O_<sort>
        case IExpression.EqLit(IFunApp(ADT.CtorId(_, _), Seq(_)), _) =>
          returnDefault

        case e @ IEquation(term1, term2) =>
          (subres :+ ValSet(term1, term2)).reduce(
            ValSet.merge(_, _)
          )

        case e @ IIntFormula(IIntRelation.EqZero, term) =>
          (subres :+ ValSet(0, term)).reduce(
            ValSet.merge(_, _)
          )

        case default =>
          returnDefault
      }
    }
  }

  // skips all quantified variables (as they don't 'exist' outside formula)
  object DeBrujinReader
      extends CollectingVisitor[Int, ValSet]
      with ExpressionUtils {

    override def preVisit(
        t: IExpression,
        quantifierDepth: Int
    ): PreVisitResult = t match {
      case vb: IVariableBinder =>
        UniSubArgs(quantifierDepth + 1)
      case _ =>
        KeepArg
    }

    override def postVisit(
        t: IExpression,
        quantifierDepth: Int,
        subres: Seq[ValSet]
    ): ValSet = {
      def returnDefault = subres.size match {
        case 0 => ValSet.empty
        case _ => subres.reduce(ValSet.merge(_, _))
      }

      def shiftTerm(term: ITerm, quantifierDepth: Int): ITerm = {
        VariableShiftVisitor(term, quantifierDepth, -quantifierDepth)
      }

      t match {
        // skip is_O_<sort>
        case IExpression.EqLit(IFunApp(ADT.CtorId(_, _), Seq(_)), _) =>
          returnDefault

        case e @ IEquation(term1, term2)
            if !ContainsQuantifiedVisitor(term1, quantifierDepth)
              && !ContainsQuantifiedVisitor(term2, quantifierDepth) =>
          val shiftedTerm1 = shiftTerm(term1, quantifierDepth)
          val shiftedTerm2 = shiftTerm(term2, quantifierDepth)
          (subres :+ ValSet(shiftedTerm1, shiftedTerm2)).reduce(
            ValSet.merge(_, _)
          )

        case e @ IIntFormula(IIntRelation.EqZero, term)
            if !ContainsQuantifiedVisitor(term, quantifierDepth) =>
          val shiftedTerm = shiftTerm(term, quantifierDepth)
          (subres :+ ValSet(0, shiftedTerm)).reduce(
            ValSet.merge(_, _)
          )

        case default =>
          returnDefault
      }
    }

  }
}
