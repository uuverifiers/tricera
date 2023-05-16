package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import ap.theories.Heap.HeapFunExtractor
import ap.theories.ADT
import ap.theories.Heap
import ap.theories.Theory
import ContractConditionType._
import ap.types.MonoSortedIFunction
import tricera.acsl.ACSLTranslator.{FunctionContext => ACSLFunctionContext}

object ACSLExpressionProcessor
    extends ContractProcessor
    with ContractConditionTools {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    apply(cci.solution, cci.predicate, cci.context)
  }

  def apply(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      context: FunctionContext
  ): IExpression = {
    val acslArgNames = getACSLArgNames(predicate, context)
    val contractCondition = solution(predicate)
    val contractConditionType = getContractConditionType(predicate, context)
    val paramNames = context.acslContext.getParams.map(x => x.name)
    val acslFunctionContext = context.acslContext
    val visitor =
      new ACSLExpressionVisitor(
        contractConditionType,
        acslArgNames,
        paramNames,
        acslFunctionContext
      )
    visitor(contractCondition)
  }

  class ACSLExpressionVisitor(
      contractConditionType: ContractConditionType,
      acslArgNames: Seq[String],
      paramNames: Seq[String],
      acslFunctionContext: ACSLFunctionContext
  ) extends CollectingVisitor[Int, IExpression]
      with ExpressionUtils {

    def apply(contractCondition: IExpression): IExpression = {
      visit(contractCondition, 0)
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

      def isSelector(
          function: MonoSortedIFunction,
          acslFunctionContext: ACSLFunctionContext
      ): Boolean = {
        val selectors = acslFunctionContext.getStructMap.values.map((struct) => struct.sels.map(_._1)).toSet.flatten
        selectors.contains(function)
      }

      t match {
        // NOTE: getSort and O_ are not theory of heap functions

        // is_O_<sort>(read(@h, p)) -> \valid(p)
        // FIX: ADT.CtorId(adt, sortNum) might match on default object
        case Is_O_Sort(
              TheoryOfHeapFunApp(
                readFun,
                heapTheory,
                Seq(Var(h), Var(p))
              )
            )
            if (isReadFun(readFun, heapTheory) &&
              isHeap(h, quantifierDepth, acslArgNames)) => {
          if (
            isPostcondition(contractConditionType) &&
            isParam(p, quantifierDepth, acslArgNames, paramNames)
          ) {
            t update subres
          } else {
            IAtom(ACSLExpression.valid, Seq(p))
          }
        }

        // get<sort>(field(read(h,p))) ~> p->field: how to tell whether an ADT function is a field selector?
        case IFunApp(
              selector: MonoSortedIFunction,
              Seq(
                IFunApp(
                  getFun,
                  Seq(
                    TheoryOfHeapFunApp(
                      readFun,
                      heapTheory,
                      Seq(Var(h), Var(p))
                    )
                  )
                )
              )
            )
            if (isGetSortFun(getFun) &&
              isReadFun(readFun, heapTheory) &&
              isSelector(selector, acslFunctionContext) &&
              (isHeap(h, quantifierDepth, acslArgNames) ||
                isOldHeap(h, quantifierDepth, acslArgNames))) =>
          contractConditionType match {
            case Precondition =>
              ACSLExpression.arrowFunApp(
                ACSLExpression.arrow,
                p,
                selector,
                quantifierDepth,
                acslArgNames
              )
            case Postcondition =>
              (
                isOldHeap(h, quantifierDepth, acslArgNames),
                isOldVar(p, quantifierDepth, acslArgNames),
                isParam(p, quantifierDepth, acslArgNames, paramNames)
              ) match {
                case (false, false, false) =>
                  // read(@h, p), p not param => p->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrow,
                    p,
                    selector,
                    quantifierDepth,
                    acslArgNames
                  )
                case (false, true, true) =>
                  // read(@h, p_0), p is param => p->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrow,
                    p,
                    selector,
                    quantifierDepth,
                    acslArgNames
                  )
                case (false, true, false) =>
                  // read(@h, p_0), p not param => \old(p)->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrowOldPointer,
                    p,
                    selector,
                    quantifierDepth,
                    acslArgNames
                  )
                case (true, true, true) =>
                  // read(@h_0, p_0), p is param => \old(p->a)
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.oldArrow,
                    p,
                    selector,
                    quantifierDepth,
                    acslArgNames
                  )
                case (true, true, false) =>
                  // read(@h_0, p_0), p not param => \old(p->a)
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.oldArrow,
                    p,
                    selector,
                    quantifierDepth,
                    acslArgNames
                  )
                case _ => t update subres
              }
          }

        // read(h,p).get_<sort> ~> *p
        case IFunApp(
              getFun,
              Seq(
                TheoryOfHeapFunApp(
                  readFun,
                  heapTheory,
                  Seq(Var(h), Var(p))
                )
              )
            )
            if (isGetSortFun(getFun) &&
              isReadFun(readFun, heapTheory) &&
              (isHeap(h, quantifierDepth, acslArgNames) ||
                isOldHeap(h, quantifierDepth, acslArgNames))) => {
          contractConditionType match {
            case Precondition =>
              ACSLExpression.derefFunApp(
                ACSLExpression.deref,
                p,
                quantifierDepth,
                acslArgNames
              )
            case Postcondition =>
              (
                isOldHeap(h, quantifierDepth, acslArgNames),
                isOldVar(p, quantifierDepth, acslArgNames),
                isParam(p, quantifierDepth, acslArgNames, paramNames)
              ) match {
                case (false, false, false) => // read(@h, p), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.deref,
                    p,
                    quantifierDepth,
                    acslArgNames
                  )
                case (false, true, true) => // read(@h, p_0), p is param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.deref,
                    p,
                    quantifierDepth,
                    acslArgNames
                  )
                case (false, true, false) => // read(@h, p_0), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.derefOldPointer,
                    p,
                    quantifierDepth,
                    acslArgNames
                  )
                case (true, true, true) => // read(@h_0, p_0), p is param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.oldDeref,
                    p,
                    quantifierDepth,
                    acslArgNames
                  )
                case (true, true, false) => // read(@h_0, p_0), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.oldDeref,
                    p,
                    quantifierDepth,
                    acslArgNames
                  )
                case _ => t update subres
              }
          }
        }

        case _ => t update subres
      }
    }
  }
}
