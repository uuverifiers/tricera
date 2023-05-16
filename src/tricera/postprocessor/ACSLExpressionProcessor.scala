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
    extends ContractProcessor {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    val visitor =
      new ACSLExpressionVisitor(cci)
    visitor(cci.contractCondition)
  }

  class ACSLExpressionVisitor(
      cci: ContractConditionInfo
  ) extends CollectingVisitor[Int, IExpression] {

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

      t match {
        // NOTE: getSort and O_ are not theory of heap functions

        // is_O_<sort>(read(@h, p)) -> \valid(p)
        // FIX: ADT.CtorId(adt, sortNum) might match on default object
        case Is_O_Sort(
              TheoryOfHeapFunApp(
                readFun,
                Seq(Var(h), Var(p))
              )
            )
            if (cci.isReadFun(readFun) &&
              cci.isHeap(h, quantifierDepth)) => {
          if (
            cci.isPostcondition &&
            cci.isParam(p, quantifierDepth)
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
                      Seq(Var(h), Var(p))
                    )
                  )
                )
              )
            )
            if (cci.isGetter(getFun) &&
              cci.isReadFun(readFun) &&
              cci.isSelector(selector) &&
              (cci.isHeap(h, quantifierDepth) ||
                cci.isOldHeap(h, quantifierDepth))) =>
          cci.contractConditionType match {
            case Precondition =>
              ACSLExpression.arrowFunApp(
                ACSLExpression.arrow,
                p,
                selector,
                quantifierDepth,
                cci
              )
            case Postcondition =>
              (
                cci.isOldHeap(h, quantifierDepth),
                cci.isOldVar(p, quantifierDepth),
                cci.isParam(p, quantifierDepth)
              ) match {
                case (false, false, false) =>
                  // read(@h, p), p not param => p->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrow,
                    p,
                    selector,
                    quantifierDepth,
                    cci
                  )
                case (false, true, true) =>
                  // read(@h, p_0), p is param => p->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrow,
                    p,
                    selector,
                    quantifierDepth,
                    cci
                  )
                case (false, true, false) =>
                  // read(@h, p_0), p not param => \old(p)->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrowOldPointer,
                    p,
                    selector,
                    quantifierDepth,
                    cci
                  )
                case (true, true, true) =>
                  // read(@h_0, p_0), p is param => \old(p->a)
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.oldArrow,
                    p,
                    selector,
                    quantifierDepth,
                    cci
                  )
                case (true, true, false) =>
                  // read(@h_0, p_0), p not param => \old(p->a)
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.oldArrow,
                    p,
                    selector,
                    quantifierDepth,
                    cci
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
                  Seq(Var(h), Var(p))
                )
              )
            )
            if (cci.isGetter(getFun) &&
              cci.isReadFun(readFun) &&
              (cci.isHeap(h, quantifierDepth) ||
                cci.isOldHeap(h, quantifierDepth))) => {
          cci.contractConditionType match {
            case Precondition =>
              ACSLExpression.derefFunApp(
                ACSLExpression.deref,
                p,
                quantifierDepth,
                cci
              )
            case Postcondition =>
              (
                cci.isOldHeap(h, quantifierDepth),
                cci.isOldVar(p, quantifierDepth),
                cci.isParam(p, quantifierDepth)
              ) match {
                case (false, false, false) => // read(@h, p), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.deref,
                    p,
                    quantifierDepth,
                    cci
                  )
                case (false, true, true) => // read(@h, p_0), p is param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.deref,
                    p,
                    quantifierDepth,
                    cci
                  )
                case (false, true, false) => // read(@h, p_0), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.derefOldPointer,
                    p,
                    quantifierDepth,
                    cci
                  )
                case (true, true, true) => // read(@h_0, p_0), p is param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.oldDeref,
                    p,
                    quantifierDepth,
                    cci
                  )
                case (true, true, false) => // read(@h_0, p_0), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.oldDeref,
                    p,
                    quantifierDepth,
                    cci
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
