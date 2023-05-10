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
    extends IExpressionProcessor
    with ContractConditionTools {
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): IExpression = {
    val contractCondition = solution(predicate)
    val contractConditionType = getContractConditionType(predicate, context)
    val acslArgNames = getACSLArgNames(predicate, context)
    val acslFunctionContext = context.acslContext
    val theoryOfHeapRewriter = new TheoryOfHeapRewriter(
      contractConditionType,
      acslArgNames,
      acslFunctionContext
    )

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

    iterateUntilFixedPoint(contractCondition, theoryOfHeapRewriter.apply)
  }

  class TheoryOfHeapRewriter(
      contractConditionType: ContractConditionType,
      acslArgNames: Seq[String],
      acslContext: ACSLFunctionContext
  ) extends CollectingVisitor[Int, IExpression]
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
          isOldHeap(v, quantifierDepth, acslArgNames)
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

      def getGetter(heapTerm: ITerm): Option[IFunction] = {
        heapTerm match {
          case IFunApp(wrapper, _) =>
            acslContext.wrapperSort(wrapper) match {
              case Some(sort) =>
                acslContext.sortGetter(sort)
              case _ => None
            }
          case _ => None
        }
      }

      def assignmentToEquality(
          pointer: ITerm,
          value: ITerm,
          heapVar: ISortedVariable,
          heapTheory: Heap
      ): Option[IFormula] = {
        getGetter(value) match {
          case Some(selector) =>
            Some(
              IEquation(
                IFunApp(
                  selector,
                  Seq(IFunApp(heapTheory.read, Seq(heapVar, pointer)))
                ),
                IFunApp(selector, Seq(value))
              ).asInstanceOf[IFormula]
            )
          case _ => None
        }
      }

      def extractEqualitiesFromWriteChain(
          funApp: IExpression,
          heapVar: ISortedVariable,
          heapTheory: Heap
      ) = {
        getAssignments(funApp)
          .map { case (pointer, value) =>
            assignmentToEquality(pointer, value, heapVar, heapTheory) match {
              case Some(eq) => eq
            }
          }
          .reduce(_ & _)
      }

      t match {
        // write(write(...write(@h, ptr1, val1)...)) -> read(@h, ptr1) == val1 && read(@h, ptr2) == val2 && ...
        // addresses must be separated and pointers valid

        case IEquation(
              heapFunApp @ TheoryOfHeapFunApp(function, heapTheory, _),
              Var(h)
            )
            if (leadsToOldHeap(
              heapFunApp,
              quantifierDepth
            ) && isHeap(h, quantifierDepth, acslArgNames)) =>
          extractEqualitiesFromWriteChain(heapFunApp, h, heapTheory)
        // other order..
        case IEquation(
              Var(h),
              heapFunApp @ TheoryOfHeapFunApp(function, heapTheory, _)
            )
            if (leadsToOldHeap(
              heapFunApp,
              quantifierDepth
            ) && isHeap(h, quantifierDepth, acslArgNames)) =>
          extractEqualitiesFromWriteChain(heapFunApp, h, heapTheory)

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
        case TheoryOfHeapFunApp(
              readFun,
              heapTheory,
              Seq(TheoryOfHeapFunApp(writeFun, _, Seq(Var(h), p2, o)), p1)
            )
            if (isReadFun(readFun, heapTheory)
              && isWriteFun(writeFun, heapTheory)
              && p1 == p2) =>
          o

        case _ => t update subres
      }
    }
  }

}
