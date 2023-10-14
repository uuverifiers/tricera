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

/* TheoryOfHeapProcessor.scala
 *  
 * See TOHProcessor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 * 
 * In this contract processor, theory of heap expressions are reduced to a simpler form 
 * containing fewer subexpressions, which can be handled by the ADTSimplifier, 
 * ADTExploder and ACSLExpressionProcessor.
 */

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
