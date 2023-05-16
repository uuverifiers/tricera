package tricera.postprocessor

import tricera.postprocessor.ContractConditionType._
import ap.parser._

object AssignmentProcessor extends ContractProcessor {
  def processContractCondition(cci: ContractConditionInfo) = {
    cci.contractConditionType match {
      case Precondition =>
        cci.contractCondition
      case Postcondition =>
        (new AssignmentProcessor(cci)).visit(cci.contractCondition, 0)
    }
  }
}

class AssignmentProcessor(cci: ContractConditionInfo)
    extends CollectingVisitor[Int, IExpression] {

  private def getAssignments(t: IExpression): Seq[(ITerm, ITerm)] = {
    t match {
      case IFunApp(
            writeFun,
            Seq(heap, pointer, value)
          ) if (cci.isWriteFun(writeFun)) =>
        val assignment =
          (pointer.asInstanceOf[ITerm], value.asInstanceOf[ITerm])
        assignment +: getAssignments(heap)
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
  ) = {
    val assignments = getAssignments(funApp)
      .map { case (pointer, value) =>
        assignmentToEquality(pointer, value, heapVar).get
      }
    assignments.size match {
      case s if s >= 2 =>
        assignments.reduce(_ & _)
      case 1 =>
        assignments.head
      case _ => IBoolLit(true)
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
      subres: Seq[IExpression]
  ): IExpression = {
    t match {
      // write(write(...write(@h, ptr1, val1)...)) -> read(@h, ptr1) == val1 && read(@h, ptr2) == val2 && ...
      // addresses must be separated and pointers valid
      case IEquation(
            heapFunApp @ TheoryOfHeapFunApp(function, _),
            Var(h)
          ) if cci.isHeap(h, quantifierDepth) =>
        extractEqualitiesFromWriteChain(heapFunApp, h)
      // other order..
      case IEquation(
            Var(h),
            heapFunApp @ TheoryOfHeapFunApp(function, _)
          ) if cci.isHeap(h, quantifierDepth) =>
        extractEqualitiesFromWriteChain(heapFunApp, h)

      case _ => t update subres
    }
  }
}
