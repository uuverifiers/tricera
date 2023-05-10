package tricera.postprocessor

import ap.parser._
import IExpression.Predicate
import tricera.concurrency.CCReader.FunctionContext
import tricera.concurrency.ccreader.CCStruct
import ap.theories.ADT.ADTProxySort
import ap.theories.{ADT, TheoryRegistry}
import ap.types.{MonoSortedIFunction, SortedConstantTerm}
import tricera.acsl.ACSLTranslator.{FunctionContext => ACSLFunctionContext}

object ADTSimplifier extends IExpressionProcessor {
  def process(
      solution: SolutionProcessor.Solution,
      predicate: Predicate,
      function: String,
      context: FunctionContext
  ): IExpression = {
    val expr = solution(predicate)
    val acslFunctionContext = context.acslContext
    apply(expr, acslFunctionContext)
  }

  def apply(
      expr: IExpression,
      acslFunctionContext: ACSLFunctionContext
  ): IExpression = {
    val adtTermSimplifier = new ADTTermSimplifier(
      acslFunctionContext: ACSLFunctionContext
    )
    adtTermSimplifier.visit(expr, null)
  }

  class ADTTermSimplifier(acslFunctionContext: ACSLFunctionContext)
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
        acslFunctionContext.getStruct(constructor) match {
          case Some(struct) =>
            val index = struct.sels.map(_._1).indexOf(selector)
            fields.lift(index)
          case _ => None
        }
      }

      def isStructCtor(
          fun: MonoSortedIFunction,
          acslFunctionContext: ACSLFunctionContext
      ): Boolean = {
        acslFunctionContext
          .getStruct(fun)
          .isDefined
      }

      def structHasField(
          constructor: MonoSortedIFunction,
          selector: MonoSortedIFunction,
          acslFunctionContext: ACSLFunctionContext
      ) = {
        acslFunctionContext
          .getStruct(constructor) match {
          case Some(s) =>
            s.sels.map((ctorAndType) => ctorAndType._1).contains(selector)
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
            if isStructCtor(structCtor, acslFunctionContext) && structHasField(
              structCtor,
              selFun,
              acslFunctionContext
            ) =>
          println("match! " + t)
          getField(selFun, structCtor, fields) match {
            case Some(x) => x
          }

        case _ =>
          t update subres
      }
    }
  }
}
