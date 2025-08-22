/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025 Scania CV AB
 *               2025 Zafer Esen. All rights reserved.
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
import ap.parser.IExpression.i

import tricera._


class PointerPropProcessor(srcs : Seq[FunctionInvariants]) extends ResultProcessor {
  import tricera.postprocessor.PointerTools._

  override def applyTo(target: Solution) = target match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(applyTo), loopInvariants)
  }

  private def applyTo(funcInvs : FunctionInvariants) : FunctionInvariants = {
    srcs.find(_.id == funcInvs.id) match {
      case Some(srcInv) =>
        val preSafePointers = inferSafeHeapPointers(srcInv.preCondition)

        val augmentedPre = addPtrAtoms(
          targetInv = funcInvs.preCondition.invariant,
          safePtrs = preSafePointers
        )

        val fullValSet = ValSet.union(
          ValSetReader(srcInv.preCondition.invariant.expression),
          ValSetReader(srcInv.postCondition.invariant.expression)
        )

        val augmentedPost = addPostConditionPtrAtoms(
          post = funcInvs.postCondition,
          preSafePointers = preSafePointers,
          valSet = fullValSet
        )

        val newInvs = funcInvs.copy(
          preCondition = PreCondition(augmentedPre),
          postCondition = PostCondition(augmentedPost)
        )
        DebugPrinter.oldAndNew(this, funcInvs, newInvs)
        newInvs

      case None =>
        funcInvs
    }
  }

  private def addPtrAtoms(targetInv : Invariant, safePtrs : Set[ProgVarProxy])
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

  private def addPostConditionPtrAtoms(post            : PostCondition,
                                       preSafePointers : Set[ProgVarProxy],
                                       valSet          : ValSet) : Invariant = {
    val postSafePointersFromEquiv = preSafePointers.flatMap { p_pre =>
      val equivPostVars: Set[ProgVarProxy] = valSet.getVal(i(p_pre)) match {
        case Some(equivClass) =>
          Set(equivClass.variants.collect {
            case IConstant(p_post: ProgVarProxy) if p_post.isPostExec => p_post
          }.head) // only use one value from eq. class
        case None =>
          Set.empty
      }
      equivPostVars
    }

    val postSafePointers =
      inferSafeHeapPointers(post).filter(p => p.isPostExec)
    addPtrAtoms(post.invariant, postSafePointers union postSafePointersFromEquiv)
  }
}
