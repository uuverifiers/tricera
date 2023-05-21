package tricera.postprocessor

import ap.parser._
import ap.terfor.ConstantTerm
import IExpression._
import ap.types.MonoSortedIFunction

object ACSLExpression {
  val valid = new Predicate("\\valid", 1)
  val deref = new IFunction("deref", 1, false, false) // *p
  val oldDeref = new IFunction("oldDeref", 1, false, false) // \old(*p)
  val derefOldPointer =
    new IFunction("derefOldPointer", 1, false, false) // *\old(p)
  val arrow = new IFunction("arrow", 2, false, false) // p->a
  val arrowOldPointer =
    new IFunction("arrowOldPointer", 2, false, false) // \old(p)->a
  val oldArrow = new IFunction("oldArrow", 2, false, false) // \old(p)->a
  val separated = new Predicate("\\separated", 2) // \separated(p1, p2)

  val functions = Set(deref, oldDeref, derefOldPointer, arrow, arrowOldPointer, oldArrow)
  val predicates = Set(valid, separated)

  // Here a ConstantTerm is introduced as a container for the variable name
  def derefFunApp(
      derefFunction: IFunction,
      pointer: ISortedVariable,
      quantifierDepth: Int,
      cci: ContractConditionInfo
  ) = {
    val name = cci.stripOld(cci.getVarName(pointer, quantifierDepth).get)
    IFunApp(derefFunction, Seq(IConstant(new ConstantTerm(name))))
  }

  def arrowFunApp(
      arrowFunction: IFunction,
      pointer: ISortedVariable,
      selector: MonoSortedIFunction,
      quantifierDepth: Int,
      cci: ContractConditionInfo
  ) = {
    val pointerName = cci.stripOld(
      cci.getVarName(pointer, quantifierDepth).get
    )
    val selectorName = selector.name
    IFunApp(
      arrowFunction,
      Seq(
        IConstant(new ConstantTerm(pointerName)),
        IConstant(new ConstantTerm(selectorName))
      )
    )
  }

  def separatedPointers(
      pointers: Set[ISortedVariable],
      quantifierDepth: Int,
      cci: ContractConditionInfo
  ): IFormula = {

    def separatedAtom(p1: String, p2: String): IFormula = {
      IAtom(
        separated,
        Seq(IConstant(new ConstantTerm(p1)), IConstant(new ConstantTerm(p2)))
      ).asInstanceOf[IFormula]
    }

    val pointerNames = variableSetToRawNameSeq(pointers, quantifierDepth, cci)
    if (pointerNames.size >= 2) {
      pointerNames
        .combinations(2)
        .map({ case Seq(p1, p2) =>
          separatedAtom(p1, p2)
        })
        .reduceLeft(_ & _)
    } else {
      IBoolLit(true)
    }
  }

  def validPointers(
      pointers: Set[ISortedVariable],
      quantifierDepth: Int,
      cci: ContractConditionInfo
  ): IFormula = {
    def validAtom(p: String) = {
      IAtom(valid, Seq(IConstant(new ConstantTerm(p)))).asInstanceOf[IFormula]
    }

    val pointerNames = variableSetToRawNameSeq(pointers, quantifierDepth, cci)
    pointerNames.size match {
      case s if s >= 2 =>
        pointerNames
          .map((p) => validAtom(p))
          .reduceLeft(_ & _)
      case s if s == 1 =>
        validAtom(pointerNames.head)
      case _ => IBoolLit(true)
    }
  }

  def variableSetToRawNameSeq(
      variableSet: Set[ISortedVariable],
      quantifierDepth: Int,
      cci: ContractConditionInfo
  ): Seq[String] = {
    variableSet
      .map(pointer =>
        cci.stripOld(cci.getVarName(pointer, quantifierDepth).get)
      )
      .toSeq
  }
}
