package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.concurrency.ccreader.CCStruct
import ap.theories.ADT.ADTProxySort
import ap.theories.{ADT, TheoryRegistry}
import ap.types.{MonoSortedIFunction, SortedConstantTerm}
import tricera.acsl.ACSLTranslator.{FunctionContext => ACSLFunctionContext}

object ADTSimplifier extends ContractProcessor {
  def processContractCondition(
      cci: ContractConditionInfo
  ): IExpression = {
    apply(cci)
  }

  def apply(
      cci: ContractConditionInfo
  ): IExpression = {
    val adtTermSimplifier = new ADTTermSimplifier(cci)
    adtTermSimplifier.visit(cci.contractCondition, null)
  }

  class ADTTermSimplifier(cci: ContractConditionInfo)
      extends CollectingVisitor[Object, IExpression] {

    override def postVisit(
        t: IExpression,
        none: Object,
        subres: Seq[IExpression]
    ): IExpression = {

      import IExpression._

      def getField(
          selector: MonoSortedIFunction,
          constructor: MonoSortedIFunction,
          fields: Seq[ITerm]
      ): Option[ITerm] = {
        cci.acslContext.getStructMap.get(constructor) match {
          case Some(struct) =>
            val index = struct.sels.map(_._1).indexOf(selector)
            fields.lift(index)
          case _ => None
        }
      }

      def structHasField(
          constructor: MonoSortedIFunction,
          selector: MonoSortedIFunction,
          acslContext: ACSLFunctionContext
      ) = {
        acslContext.getStructMap.get(constructor) match {
          case Some(struct) =>
            struct.sels.map(_._1).contains(selector)
          case _ => false
        }
      }

      t match {
        // S(x,y).a -> x
        case f @ IFunApp(
              selFun: MonoSortedIFunction,
              Seq(
                structCtorFunApp @ IFunApp(
                  structCtor: MonoSortedIFunction,
                  fields
                )
              )
            )
            if cci.isStructCtor(structCtor)
              && structHasField(structCtor, selFun, cci.acslContext) =>
          getField(selFun, structCtor, fields).get

        case _ =>
          t update subres
      }
    }
  }
}
