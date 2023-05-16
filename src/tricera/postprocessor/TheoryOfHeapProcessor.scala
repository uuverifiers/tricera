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
    extends ContractProcessor {
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
  ) extends CollectingVisitor[Unit, IExpression] {

    def apply(contractCondition: IExpression): IExpression = {
      visit(contractCondition, ())
    }

    override def postVisit(
        t: IExpression,
        arg: Unit,
        subres: Seq[IExpression]
    ): IExpression = t match {

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
