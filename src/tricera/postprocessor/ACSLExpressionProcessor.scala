/**
 * Copyright (c) 2023 Oskar Soederberg. All rights reserved.
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

 /* ACSLExpressionProcessor.scala
 *
 * See ACSLProcessor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 * 
 * In this contract processor, theory of heap expressions are translated to ACSL
 * expressions.
 * 
 */

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
  ): IFormula = {
    val visitor =
      new ACSLExpressionVisitor(cci)
    visitor(cci.contractCondition)
  }

  class ACSLExpressionVisitor(
      cci: ContractConditionInfo
  ) extends CollectingVisitor[Int, IExpression] {

    def apply(contractCondition: IFormula): IFormula = {
      visit(contractCondition, 0).asInstanceOf[IFormula]
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
              (cci.isCurrentHeap(h, quantifierDepth) ||
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
              (cci.isCurrentHeap(h, quantifierDepth) ||
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
