package tricera.postprocessor

import ap.parser._
import ap.theories.ADT
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.Heap
import ap.theories.Heap.HeapFunExtractor
import ContractConditionType._
import tricera.acsl.ACSLTranslator.{FunctionContext => ACSLFunctionContext}
import ap.types.Sort

object TheoryOfHeapProcessor
    extends ContractProcessor
 {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    TheoryOfHeapRewriter(cci)
  }

  object TheoryOfHeapRewriter extends ExpressionUtils {
    def apply(cci: ContractConditionInfo): IExpression = {
      val theoryOfHeapRewriter = new TheoryOfHeapRewriter(cci)
      iterateUntilFixedPoint(cci.contractCondition, theoryOfHeapRewriter.apply)
    }
  }

  class TheoryOfHeapRewriter(
      cci: ContractConditionInfo
  ) extends CollectingVisitor[Int, IExpression] {

    def apply(contractCondition: IExpression): IExpression = {
      visit(contractCondition, 0)
    }

    private def leadsToOldHeap(
        t: IExpression,
        quantifierDepth: Int
    ): Boolean = {
      import IExpression._
      t match {
        case v @ ISortedVariable(vIndex, _) =>
          cci.isOldHeap(v, quantifierDepth)
        case IFunApp(writeFun, args)
            if (cci.isWriteFun(writeFun)) =>
          leadsToOldHeap(args.head, quantifierDepth)
        case _ => false
      }
    }

    private def getAssignments(t: IExpression): Seq[(ITerm, ITerm)] = {
      import IExpression._
      t match {
        case IFunApp(
              writeFun,
              Seq(heap, pointer, value)
            ) if (cci.isWriteFun(writeFun)) =>
          val assignment =
            (pointer.asInstanceOf[ITerm], value.asInstanceOf[ITerm])
          assignment +: getAssignments(
            heap
          ) // handle case where same pointer occurs twice (should be ruled out be rewriting rule)
        case _ => Seq()
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
        getAssignments(funApp)
          .map { case (pointer, value) =>
            assignmentToEquality(pointer, value, heapVar) match {
              case Some(eq) => eq
            }
          }
          .reduce(_ & _)
      }

      t match {
        // write(write(...write(@h, ptr1, val1)...)) -> read(@h, ptr1) == val1 && read(@h, ptr2) == val2 && ...
        // addresses must be separated and pointers valid

        case IEquation(
              heapFunApp @ TheoryOfHeapFunApp(function, _),
              Var(h)
            )
            if (leadsToOldHeap(
              heapFunApp,
              quantifierDepth
            ) && cci.isHeap(h, quantifierDepth)) =>
          extractEqualitiesFromWriteChain(heapFunApp, h)
        // other order..
        case IEquation(
              Var(h),
              heapFunApp @ TheoryOfHeapFunApp(function, _)
            )
            if (leadsToOldHeap(
              heapFunApp,
              quantifierDepth
            ) && cci.isHeap(h, quantifierDepth)) =>
          extractEqualitiesFromWriteChain(heapFunApp, h)

        // o.get<sort>.O_<sort> -> o
        case IFunApp(wrapper, Seq(IFunApp(getter, Seq(obj))))
            if (cci.isWrapper(wrapper)
              && cci.isGetter(getter)) =>
          obj

        // o.O_<sort>.get<sort> -> o
        case IFunApp(getter, Seq(IFunApp(wrapper, Seq(obj))))
            if (cci.isWrapper(wrapper)
              && cci.isGetter(getter)) =>
          obj

        // read(write(h,p,o),p) -> o
        case TheoryOfHeapFunApp(
              readFun,
              Seq(TheoryOfHeapFunApp(writeFun, Seq(Var(h), p2, o)), p1)
            )
            if (cci.isReadFun(readFun)
              && cci.isWriteFun(writeFun)
              && p1 == p2) =>
          o

        case _ => t update subres
      }
    }
  }

}
