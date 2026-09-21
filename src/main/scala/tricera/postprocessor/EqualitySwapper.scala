/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025-2026 Zafer Esen. All rights reserved.
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

 /* EqualitySwapper.scala
 * 
 * Defines objects and classes for converting expressions to equivalent 
 * representations. The ToVariableForm processor is defined here.
 *
 * See ToVariableForm in "Automated Inference of ACSL Contracts for 
 * Programs with Heaps" by Oskar Söderberg
 */

package tricera.postprocessor

import ap.parser._
import tricera._

object ToVariableForm extends ResultProcessor {

  override def applyTo(solution: Solution) = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(functionInvariants.map(applyTo), loopInvariants)
  }

  private def applyTo(funcInvs: FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      PreCondition(preInv),
      PostCondition(postInv),
      loopInvariants) =>
      val preCondValSet = ValSetReader(preInv.expression)
      val postCondValSet = ValSet.union(preCondValSet,
                                        ValSetReader(postInv.expression))
      val newInvs = FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(toVariableForm(preInv, preCondValSet)),
        PostCondition(toVariableForm(postInv, postCondValSet)),
        loopInvariants)
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  private def toVariableForm(invariant : Invariant,
                     valueSet : ValSet) : Invariant = invariant match {
    case Invariant(form, maybeHeapInfo, maybeSourceInfo) =>
      Invariant(
        EqualitySwapper(
          normaliseReadAddresses(form, valueSet, maybeHeapInfo),
          valueSet.toCanonicalFormMap,
          maybeHeapInfo).asInstanceOf[IFormula],
        maybeHeapInfo,
        maybeSourceInfo)
  }

  private def normaliseReadAddresses(form : IFormula, values : ValSet,
                                     heapInfo : Option[HeapInfo]) : IFormula = {
    // Use known values inside addresses, e.g., size(h1) = size(h0) = 3.
    // Only replace terms by constants or literals, so rewriting cannot grow terms.
    val replacements : Map[IExpression, ITerm] = values.vals.flatMap { value =>
      value.variants.collect {
        case t : IConstant => t : ITerm
        case t : IIntLit => t : ITerm
      }.minByOption(values.getOrderingKey).toSeq.flatMap { rep =>
        value.variants.filterNot(_ == rep).map(_ -> rep)
      }
    }.toMap
    val canonical = values.toCanonicalFormMap
    def resolve(address : ITerm, info : HeapInfo) : ITerm = {
      val simplified = new Simplifier().apply(Rewriter.rewrite(address,
        t => replacements.getOrElse(t, t)).asInstanceOf[ITerm])
      // Native heap addresses can also occur without their addr wrapper.
      val candidates = info.heap match {
        case _ : ap.theories.heaps.NativeHeap =>
          Seq(simplified, IFunApp(info.heap.addr, Seq(simplified)))
        case _ => Seq(simplified)
      }
      candidates.iterator.map(t => canonical.getOrElse(t, t)).collectFirst {
        case p @ ConstantAsProgVarProxy(v) if v.isPointer => p
      }.getOrElse(address)
    }
    Rewriter.rewrite(form, {
      case read @ IFunApp(f, Seq(h, address))
          if heapInfo.exists(_.isReadFun(f)) &&
             SymbolCollector.variables(address).isEmpty =>
        val resolved = resolve(address, heapInfo.get)
        if (resolved == address) read else IFunApp(f, Seq(h, resolved))
      case t => t
    }).asInstanceOf[IFormula]
  }
}

object ToExplicitForm {
  def apply(expr : IExpression, valueSet : ValSet) =
    EqualitySwapper(expr, valueSet.toCanonicalFormMap)
}

object EqualitySwapper {
  def apply(expr : IExpression, swapMap : Map[IExpression, ITerm],
            heapInfo : Option[HeapInfo] = None) =
    (new EqualitySwapper(swapMap, heapInfo))(expr)
}

class EqualitySwapper(swapMap : Map[IExpression, ITerm],
                      heapInfo : Option[HeapInfo] = None)
    extends CollectingVisitor[Int, IExpression]
    with ExpressionUtils {
  def apply(contractCondition : IExpression) : IExpression = {
    def rewriter(expr : IExpression) : IExpression = {
      visit(expr, 0)
    }
    iterateUntilFixedPoint(contractCondition, rewriter)
  }

  override def preVisit(t               : IExpression,
                        quantifierDepth : Int) : PreVisitResult = t match {
    case _ : IVariableBinder => UniSubArgs(quantifierDepth + 1)
    case _                   => KeepArg
  }

  override def postVisit(t               : IExpression,
                         quantifierDepth : Int,
                         subres          : Seq[IExpression]) : IExpression = {
    val updated = t update subres
    (updated, swapMap.getOrElse(updated, updated)) match {
      case (IFunApp(_, Seq()), swapped: IConstant) =>
        swapped
      case (IFunApp(fun, _), swapped: IConstant)
          if heapInfo.exists(_.isAddrFun(fun)) =>
        swapped
      case _ =>
        updated
    }
  }
}
