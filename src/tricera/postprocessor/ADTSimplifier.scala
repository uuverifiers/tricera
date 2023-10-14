/**
 * Copyright (c) 2011-2019 Oskar Soederberg. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

 /* ADTSimplifier.scala
 *
 * See ADTProcessor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 * 
 * In this step, struct expressions are reduced to a simpler form containing 
 * fewer subexpressions, which can be handled by the ACSLExpressionProcessor
 */

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
