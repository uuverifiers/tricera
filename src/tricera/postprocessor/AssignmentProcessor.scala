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

/* AssignmentProcessor.scala
 *  
 * See AssignmentExtractor in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 *  
 * In this contract processor, postcondition equalities between dereferenced 
 * pointers and their values are extracted. This information is extracted from 
 * assignments to the heap and can only be done whenever the post heap state is 
 * expressed. The precondition is left unchanged.
 */

package tricera.postprocessor

import ap.parser._
import ap.terfor.ConstantTerm

import tricera.{
  ConstantAsProgVarProxy, FunctionInvariants, HeapInfo,
  Invariant, InvariantContext, LoopInvariant, PostCondition, PreCondition,
  ProgVarProxy, Result, Solution}

import tricera.concurrency.ccreader.CCExceptions.NeedsHeapModelException


class AssignmentProcessor(srcs: Seq[FunctionInvariants]) extends ResultProcessor {
  import tricera.postprocessor.PointerTools._

  override def applyTo(solution: Solution) = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(applyTo), loopInvariants)
  }

  private def applyTo(funcInv: FunctionInvariants)
  : FunctionInvariants = funcInv match {
    case FunctionInvariants(id, isSrcAnnotated, preCondition, postCondition @ PostCondition(postInv), loopInvariants) =>
      val newInv = srcs.find(p => p.id == id) match {
        case Some(srcInv) => 
          FunctionInvariants(
            id,
            isSrcAnnotated,
            preCondition, // Note: This processor is only applicable to the post condition
            PostCondition(addAssignmentAtoms(postInv, srcInv.postCondition, postCondition.isCurrentHeap)),
            loopInvariants)
        case None =>
          funcInv
      }
      DebugPrinter.oldAndNew(this, funcInv, newInv)
      newInv
  }

  private def addAssignmentAtoms(
    invariant: Invariant,
    srcInv: InvariantContext,
    isCurrentHeap: ProgVarProxy => Boolean)
    = invariant match {
    case Invariant(form, Some(heapInfo), srcInfo) =>
      val srcExp = srcInv match {
        case PreCondition(inv) => inv.expression
        case PostCondition(inv) => inv.expression
        case LoopInvariant(exp, _, _) => exp
      }
      val visitor = new AssignmentProcessorVisitor(
        ValSetReader.deBrujin(srcExp),
        inferSafeHeapPointers(srcInv),
        isCurrentHeap,
        heapInfo)
      val newForm = visitor.visit(form, 0) match {
        case None => form
        case Some(assignments) => form.&(assignments)
      }
      Invariant(newForm, Some(heapInfo), srcInfo)
    case _ =>
      throw NeedsHeapModelException
  }
}


private class AssignmentProcessorVisitor(
  valueSet: ValSet,
  separatedSet: Set[ProgVarProxy],
  isCurrentHeap: ProgVarProxy => Boolean,
  heapInfo: HeapInfo) 
  extends CollectingVisitor[Int, Option[IFormula]] {

  private def getReverseAssignments(t: IExpression): Seq[(ITerm, ITerm)] = {
    t match {
      case IFunApp(
            writeFun,
            Seq(heap, pointer, value)
          ) if (heapInfo.isWriteFun(writeFun)) =>
        val assignment =
          (pointer.asInstanceOf[ITerm], value.asInstanceOf[ITerm])
        assignment +: getReverseAssignments(heap)
      case _ => Seq()
    }
  }

  def assignmentToEquality(
      pointer: ITerm,
      value: ITerm,
      heapVar: ProgVarProxy
  ): Option[IFormula] = {
    value match {
      case IFunApp(objCtor, _) =>
        heapInfo.objectCtorToSelector(objCtor)
          .map(selector => IEquation(
            IFunApp(
              selector,
              Seq(IFunApp(heapInfo.getReadFun, Seq(IConstant(heapVar), pointer)))
            ),
            IFunApp(selector, Seq(value))).asInstanceOf[IFormula])
      case _ => None
    }
  }

  def extractEqualitiesFromWriteChain(
      funApp: IExpression,
      heapVar: ProgVarProxy
  ): Option[IFormula] = {
    def takeWhileSeparated(assignments: Seq[(ITerm, ITerm)]) = {
      if (separatedSet.isEmpty) {
        Seq(assignments.head)
      } else {
        assignments.takeWhile { case (pointer, value) =>
          separatedSet.exists(valueSet.areEqual(pointer, _))
        }
      }
    }

    def takeFirstAddressWrites(assignments: Seq[(ITerm, ITerm)]) = {
      assignments
        .foldLeft((Set[ITerm](), Seq[(ITerm, ITerm)]())) {
          case ((seen, acc), (pointer, value)) =>
            if (seen.contains(pointer)) {
              (seen, acc)
            } else {
              (seen + pointer, acc :+ (pointer, value))
            }
        }
        ._2
    }

    val assignments = getReverseAssignments(funApp)
    val separatedAssignments = takeWhileSeparated(assignments)
    val currentAssignments = takeFirstAddressWrites(separatedAssignments)
      .map { case (pointer, value) =>
        assignmentToEquality(pointer, value, heapVar).get
      }
    currentAssignments.size match {
      case s if s >= 2 =>
        Some(currentAssignments.reduce(_ & _))
      case 1 =>
        Some(currentAssignments.head)
      case _ => None
    }
  }

  def shiftFormula(
      formula: Option[IFormula],
      quantifierDepth: Int
  ): Option[IFormula] = {
    formula match {
      case Some(f) =>
        if (ContainsQuantifiedVisitor(f, quantifierDepth)) {
          None
        } else {
          Some(VariableShiftVisitor(f, quantifierDepth, -quantifierDepth))
        }
      case None => None
    }
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
      subres: Seq[Option[IFormula]]
  ): Option[IFormula] = {
    t match {
      // write(write(...write(@h, ptr1, val1)...)) -> read(@h, ptr1) == val1 && read(@h, ptr2) == val2 && ...
      // addresses must be separated and pointers valid
      case IEquation(
            heapFunApp @ IFunApp(function, _),
            ConstantAsProgVarProxy(h)
          ) if isCurrentHeap(h) =>
        shiftFormula(
          extractEqualitiesFromWriteChain(heapFunApp, h),
          quantifierDepth
        )

      // other order..
      case IEquation(
            ConstantAsProgVarProxy(h),
            heapFunApp @ IFunApp(function, _)
          ) if isCurrentHeap(h) =>
        shiftFormula(
          extractEqualitiesFromWriteChain(heapFunApp, h),
          quantifierDepth
        )

      case _ => subres.collectFirst { case Some(h) => h }
    }
  }
}
