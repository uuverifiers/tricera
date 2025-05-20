/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025 Ola Wingbrant. All rights reserved.
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

/* PointerPropProcessor.scala
 * 
 * See PointerPropExtractor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 *
 * In this contract processor, any separation and validity clauses that can be 
 * deduced are extracted. This can only be done whenever the heap state is 
 * expressed.
 */

package tricera.postprocessor

import ap.parser._
import scala.collection.immutable.Stack
import tricera.{
  ConstantAsProgVarProxy,FunctionInvariants, HeapInfo, Invariant,
  PostCondition, PreCondition, ProgVarProxy, Result, Solution}

import tricera.concurrency.ccreader.CCExceptions.NeedsHeapModelException


class PointerPropProcessor(srcs: Seq[FunctionInvariants]) extends ResultProcessor {
  import tricera.postprocessor.PointerTools._

  override def applyTo(target: Solution) = target match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(applyTo), loopInvariants)
  }

  private def applyTo(funcInvs: FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      preCond @ PreCondition(preInv),
      postCond @ PostCondition(postInv),
      loopInvariants) =>
      val newInvs = srcs.find(p => p.id == id) match {
        case Some(srcInv) => 
          FunctionInvariants(
            id,
            isSrcAnnotated,
            PreCondition(addPtrAtoms(preInv, inferSafeHeapPointers(srcInv.preCondition))),
            PostCondition(addPtrAtoms(postInv, inferSafeHeapPointers(srcInv.postCondition))),
            loopInvariants)
        case None =>
          funcInvs
      }
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  private def addPtrAtoms(targetInv: Invariant, safePtrs: Set[ProgVarProxy])
    : Invariant = targetInv match {
    case Invariant(form, heapInfo, srcInfo) =>
      val newForm = safePtrs.size match {
        case 0 => 
          form
        case 1 =>
          form
          .&(ACSLExpression.validPointers(safePtrs))
        case _ =>
          form
          .&(ACSLExpression.separatedPointers(safePtrs))
          .&(ACSLExpression.validPointers(safePtrs))
      }
      Invariant(newForm, heapInfo, srcInfo)
    case _ =>
      targetInv
  }
}
