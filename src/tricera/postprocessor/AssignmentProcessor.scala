package tricera.postprocessor

import tricera.postprocessor.ContractConditionType._
import ap.parser._

object AssignmentProcessor extends ContractProcessor {
  def apply(
      expr: IExpression,
      valueSet: ValSet,
      separatedSet: Set[ISortedVariable],
      cci: ContractConditionInfo
  ): Option[IFormula] = {
    (new AssignmentProcessor(valueSet, separatedSet, cci)).visit(expr, 0)
  }

  def processContractCondition(cci: ContractConditionInfo) = {
    getClauses(cci.contractCondition, cci) match {
      case Some(clauses) =>
        cci.contractCondition
          .asInstanceOf[IFormula]
          .&(clauses)
      case _ =>
        cci.contractCondition
    }
  }

  def getClauses(
      expr: IExpression,
      cci: ContractConditionInfo
  ): Option[IFormula] = {
    cci.contractConditionType match {
      case Precondition =>
        None
      case Postcondition =>
        val valueSet = ValSetReader.deBrujin(cci.contractCondition)
        val separatedSet =
          PointerPropProcessor.getSafePointers(cci.contractCondition, cci)
        AssignmentProcessor(expr, valueSet, separatedSet, cci)
    }
  }
}

class AssignmentProcessor(
    valueSet: ValSet,
    separatedSet: Set[ISortedVariable],
    cci: ContractConditionInfo
) extends CollectingVisitor[Int, Option[IFormula]] {

  private def getReverseAssignments(t: IExpression): Seq[(ITerm, ITerm)] = {
    t match {
      case IFunApp(
            writeFun,
            Seq(heap, pointer, value)
          ) if (cci.isWriteFun(writeFun)) =>
        val assignment =
          (pointer.asInstanceOf[ITerm], value.asInstanceOf[ITerm])
        assignment +: getReverseAssignments(heap)
      case _ => Seq()
    }
  }

  def assignmentToEquality(
      pointer: ITerm,
      value: ITerm,
      heapVar: ISortedVariable
  ): Option[IFormula] = {
    cci.getGetter(value) match {
      case Some(selector) =>
        Some(
          IEquation(
            IFunApp(
              selector,
              Seq(IFunApp(cci.heapTheory.read, Seq(heapVar, pointer)))
            ),
            IFunApp(selector, Seq(value))
          ).asInstanceOf[IFormula]
        )
      case _ => None
    }
  }

  def extractEqualitiesFromWriteChain(
      funApp: IExpression,
      heapVar: ISortedVariable
  ): Option[IFormula] = {
    def takeWhileSeparated(assignments: Seq[(ITerm, ITerm)]) = {
      if (separatedSet.isEmpty) {
        Seq(assignments.head)
      } else {
        assignments.takeWhile { case (pointer, value) =>
          separatedSet.exists(valueSet.areEqual(pointer, _))
        }
      }
    }

    def takeFirstAddressWrites(assignments: Seq[(ITerm, ITerm)]) = {
      assignments
        .foldLeft((Set[ITerm](), Seq[(ITerm, ITerm)]())) {
          case ((seen, acc), (pointer, value)) =>
            if (seen.contains(pointer)) {
              (seen, acc)
            } else {
              (seen + pointer, acc :+ (pointer, value))
            }
        }
        ._2
    }

    val assignments = getReverseAssignments(funApp)
    val separatedAssignments = takeWhileSeparated(assignments)
    val currentAssignments = takeFirstAddressWrites(separatedAssignments)
      .map { case (pointer, value) =>
        assignmentToEquality(pointer, value, heapVar).get
      }
    currentAssignments.size match {
      case s if s >= 2 =>
        Some(currentAssignments.reduce(_ & _))
      case 1 =>
        Some(currentAssignments.head)
      case _ => None
    }
  }

  override def preVisit(
      t: IExpression,
      quantifierDepth: Int
  ): PreVisitResult = t match {
    case v: IVariableBinder => UniSubArgs(quantifierDepth + 1)
    case _                  => KeepArg
  }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[Option[IFormula]]
  ): Option[IFormula] = {
    t match {
      // write(write(...write(@h, ptr1, val1)...)) -> read(@h, ptr1) == val1 && read(@h, ptr2) == val2 && ...
      // addresses must be separated and pointers valid
      case IEquation(
            heapFunApp @ IFunApp(function, _),
            Var(h)
          ) if cci.isHeap(h, quantifierDepth) =>
        extractEqualitiesFromWriteChain(heapFunApp, h)
      // other order..
      case IEquation(
            Var(h),
            heapFunApp @ IFunApp(function, _)
          ) if cci.isHeap(h, quantifierDepth) =>
        extractEqualitiesFromWriteChain(heapFunApp, h)

      case _ => subres.collectFirst { case Some(h) => h }
    }
  }
}
