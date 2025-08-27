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

import ap.parser.{IConstant, ITerm}
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
        val augmentedPre =
          addPtrAtoms(funcInvs.preCondition.invariant, preSafePointers)

        val fullValSet = ValSet.union(
          ValSetReader(srcInv.preCondition.invariant.expression),
          ValSetReader(srcInv.postCondition.invariant.expression)
        )

        val augmentedPost =
          addPostConditionPtrAtoms(
          funcInvs.postCondition,
          preSafePointers,
          fullValSet
        )

        val newInvs = funcInvs.copy(
          preCondition  = PreCondition(augmentedPre),
          postCondition = PostCondition(augmentedPost)
        )
        DebugPrinter.oldAndNew(this, funcInvs, newInvs)
        newInvs

      case None =>
        funcInvs
    }
  }

  private def addPtrAtoms(targetInv : Invariant,
                          safePtrs  : ValSet)
  : Invariant = targetInv match {
    case Invariant(f, heapInfo, srcInfo) =>
      val allSafePtrs = safePtrs.vals.flatMap(_.variants).collect{
        case ConstantAsProgVarProxy(c) => c
      }

      if (allSafePtrs.isEmpty) {
        targetInv
      } else {
        val fWithValid = f.&(ACSLExpression.validPointers(allSafePtrs))
        val newF =
          if (safePtrs.vals.size > 1)
            fWithValid.&(ACSLExpression.separatedPointers(safePtrs))
          else
            fWithValid
        Invariant(newF, heapInfo, srcInfo)
      }
    case _ =>
      targetInv
  }

  private def addPostConditionPtrAtoms(
    post            : PostCondition,
    preSafePointers : ValSet,
    equivalences    : ValSet) : Invariant = {
    val postValsFromPre = preSafePointers.vals.flatMap { preVal =>
      preVal.variants.headOption.flatMap(p_pre => equivalences.getVal(p_pre)) match {
        case Some(equiv) =>
          val postPointers = equiv.variants.collect {
            case t @ IConstant(p : ProgVarProxy) if p.isPostExec => t
          }.map(_.asInstanceOf[ITerm])
          if (postPointers.nonEmpty) Some(Val(postPointers)) else None
        case None => None
      }
    }
    val postSafePointersFromPre = ValSet(postValsFromPre)
    val postSafePointersFromPost = inferSafeHeapPointers(post)
    val postSafePointers = ValSet.union(postSafePointersFromPre,
                                        postSafePointersFromPost)

    addPtrAtoms(post.invariant, postSafePointers)
  }
}
