package tricera.postprocessor

import ap.parser._
import ap.theories.ADT
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.Heap
import ap.theories.Heap.HeapFunExtractor

object TheoryOfHeapProcessor extends ContractConditionProcessor {
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): IExpression = {
    val contractCondition = solution(predicate)
    val contractConditionType = getContractConditionType(predicate, context)
    val acslArgNames = getACSLArgNames(predicate, context)
    val theoryOfHeapRewriter = new TheoryOfHeapRewriter(acslArgNames)
    Rewriter.rewrite(
      contractCondition,
      theoryOfHeapRewriter.apply
    ) // repeatedly applies theoryOfHeapRewriter until fixpoint reached
  }

  class TheoryOfHeapRewriter(acslArgNames: Seq[String])
      extends CollectingVisitor[Int, IExpression]
      with ExpressionUtils {

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
          isOldHeap(vIndex, quantifierDepth, acslArgNames)
        case IFunApp(writeFun @ HeapFunExtractor(heapTheory), args)
            if (isWriteFun(writeFun, heapTheory)) =>
          leadsToOldHeap(args.head, quantifierDepth)
        case _ => false
      }
    }

    private def getAssignments(t: IExpression): Seq[(ITerm, ITerm)] = {
      import IExpression._
      t match {
        case IFunApp(
              writeFun @ HeapFunExtractor(heapTheory),
              Seq(heap, pointer, value)
            ) if (isWriteFun(writeFun, heapTheory)) =>
          val assignment =
            (pointer.asInstanceOf[ITerm], value.asInstanceOf[ITerm])
          assignment +: getAssignments(
            heap
          ) // handle case where same pointer occurs twice (should be ruled out be rewriting rule)
        case _ => Seq()
      }
    }

    override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult = t match {
        case v: IVariableBinder => UniSubArgs(quantifierDepth + 1)
        case _ => KeepArg
    }

    override def postVisit(
        t: IExpression,
        quantifierDepth: Int,
        subres: Seq[IExpression]
    ): IExpression = {

      def extractEqualitiesFromWriteChain(funApp: IFunApp, heapVar: ISortedVariable, heapTheory: Heap) = {
        getAssignments(funApp)
          .map { case (pointer, value) =>
            val function = heapTheory.userADTSels(0)(
              0
            ) // HOW TO GET CORRECT TYPE?
            IEquation(
              IFunApp(function, Seq(IFunApp(heapTheory.read, Seq(heapVar, pointer)))),
              IFunApp(function, Seq(value))
            ).asInstanceOf[IFormula]
          }
          .reduce(_ & _)
      }

      t match {
        // write(write(...write(@h, ptr1, val1)...)) -> read(@h, ptr1) == val1 && read(@h, ptr2) == val2 && ...
        // addresses must be separated and pointers valid
        case IEquation(
              heapFunApp @ IFunApp(HeapFunExtractor(heapTheory), _),
              heap @ ISortedVariable(vIndex, sortToBeSelected)
            ) if (leadsToOldHeap(heapFunApp, quantifierDepth) && isHeap(vIndex, quantifierDepth, acslArgNames)) =>
          extractEqualitiesFromWriteChain(heapFunApp, heap, heapTheory)


        // o.get<sort>.O_<sort> -> o
        case IFunApp(o_SortFun, Seq(IFunApp(getSortFun, Seq(obj))))
            if (isO_SortFun(o_SortFun)
              && isGetSortFun(getSortFun)) =>
          obj

        // o.O_<sort>.get<sort> -> o
        case IFunApp(getSortFun, Seq(IFunApp(o_SortFun, Seq(obj))))
            if (isO_SortFun(o_SortFun)
              && isGetSortFun(getSortFun)) =>
          obj

        // read(write(h,p,o),p) -> o
        case IFunApp(
              readFun @ HeapFunExtractor(heapTheory),
              Seq(IFunApp(writeFun, Seq(h, p2, o)), p1)
            )
            if (isReadFun(readFun, heapTheory)
              && isWriteFun(writeFun, heapTheory)
              && p1 == p2) =>
          o

        

        case IEquation(
              heap @ ISortedVariable(vIndex, sortToBeSelected),
              heapFunApp @ IFunApp(HeapFunExtractor(heapTheory), _)
            ) if (leadsToOldHeap(heapFunApp, quantifierDepth) && isHeap(vIndex, quantifierDepth, acslArgNames)) =>
          extractEqualitiesFromWriteChain(heapFunApp, heap, heapTheory)

        case _ => t update subres
      }
    }
  }

}
