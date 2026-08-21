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
import ap.theories.ADT
import ap.types.MonoSortedIFunction
import tricera.{
  ConstantAsProgVarProxy, FunctionInvariants, HeapInfo,
  Invariant, InvariantContext, LoopInvariant, PostCondition,
  PreCondition, ProgVarProxy, Solution}

object ACSLExpressionProcessor extends ResultProcessor {

  override def applyTo(solution: Solution): Solution = solution match {
    case Solution(functionInvariants, loopInvariants) =>
      Solution(
        functionInvariants.map(applyTo(_)),
        loopInvariants.map(i => ACSLExpressionVisitor(i,i)))
  }

  private def applyTo(funcInvs: FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      preCondition @ PreCondition(preInv),
      postCondition @ PostCondition(postInv),
      loopInvariants) =>
      val newInvs = FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(ACSLExpressionVisitor(preInv, preCondition)),
        PostCondition(ACSLExpressionVisitor(postInv, postCondition)),
        loopInvariants.map(i => ACSLExpressionVisitor(i,i)))
      DebugPrinter.oldAndNew(this, funcInvs, newInvs)
      newInvs
  }

  object ACSLExpressionVisitor {
    def apply(invariant: Invariant, context: InvariantContext): Invariant =
      invariant match {
        case Invariant(form, Some(heapInfo), maybeSourceInfo) =>
          val visitor = new ACSLExpressionVisitor(heapInfo, context)
          Invariant(visitor(form), Some(heapInfo), maybeSourceInfo)
        case _ =>
          invariant
    }

    def apply(invariant: LoopInvariant, context: InvariantContext): LoopInvariant =
      invariant match {
        case LoopInvariant(form, Some(heapInfo), srcInfo) =>
          val visitor = new ACSLExpressionVisitor(heapInfo, context)
          LoopInvariant(visitor(form), Some(heapInfo), srcInfo)
        case _ =>
          invariant
    }
  }

  class ACSLExpressionVisitor(
    heapInfo: HeapInfo,
    context: InvariantContext
  ) extends CollectingVisitor[Unit, IExpression] {

    def apply(form: IFormula): IFormula = {
      visit(form, ()).asInstanceOf[IFormula]
    }

    private def isSelector(func: MonoSortedIFunction): Boolean = func match {
      case ADT.Selector(_) if !heapInfo.isObjSelector(func) => true
      case _ => false
    }

    private def isOldHeap(p: ProgVarProxy): Boolean = heapInfo.isHeap(p) && p.isPreExec

    private def isOldRange(range: ITerm): Boolean = range match {
      case ConstantAsProgVarProxy(p) => p.isPreExec
      case _ => false
    }

    private def indexedArrayAccess(address: ITerm): Option[(ITerm, ITerm)] = {
      def arrayBase(range: ITerm): ITerm = range match {
        case IFunApp(rangeSelector, Seq(base))
            if heapInfo.isArrayPointerRangeSelector(rangeSelector) => base
        case _ => range
      }

      address match {
        case IFunApp(rangeNth, Seq(range, index))
            if rangeNth == heapInfo.heap.rangeNth =>
          Some((arrayBase(range), index))
        case IPlus(index, IFunApp(rangeStart, Seq(range)))
            if heapInfo.isArrayRangeStart(rangeStart) =>
          range match {
            case IFunApp(rangeSelector, Seq(base))
                if heapInfo.isArrayPointerRangeSelector(rangeSelector) =>
              Some((base, index))
            case _ => None
          }
        case IPlus(IFunApp(rangeStart, Seq(range)), index)
            if heapInfo.isArrayRangeStart(rangeStart) =>
          range match {
            case IFunApp(rangeSelector, Seq(base))
                if heapInfo.isArrayPointerRangeSelector(rangeSelector) =>
              Some((base, index))
            case _ => None
          }
        case _ => None
      }
    }

    private def arrayElement(
        heap: ProgVarProxy,
        range: ITerm,
        index: ITerm
    ): ITerm = {
      val arrayFunction = context match {
        case _: PreCondition => ACSLExpression.arrayAccess
        case _: PostCondition =>
          (isOldHeap(heap), isOldRange(range)) match {
            case (false, false) => ACSLExpression.arrayAccess
            case (false, true) => ACSLExpression.arrayAccessOldPointer
            case (true, _) => ACSLExpression.oldArrayAccess
          }
        case _ => ACSLExpression.arrayAccess
      }
      ACSLExpression.arrayFunApp(arrayFunction, range, index)
    }

    private def indexedStructRead(term: ITerm):
        Option[(IFunction, ProgVarProxy, ITerm)] = term match {
      case IFunApp(
            getFun,
            Seq(
              TheoryOfHeapFunApp(
                readFun,
                Seq(ConstantAsProgVarProxy(h), address: ITerm)
              )
            )
          )
          if heapInfo.isObjSelector(getFun) &&
            heapInfo.isReadFun(readFun) &&
            heapInfo.isHeap(h) &&
            indexedArrayAccess(address).nonEmpty =>
        Some((getFun, h, address))
      case _ => None
    }

    private def explodeIndexedStructEquality(
        left: ITerm,
        right: ITerm
    ): Option[IFormula] = {
      val readAndValue = indexedStructRead(left)
        .map { case (getFun, heap, address) => (getFun, heap, address, right) }
        .orElse(indexedStructRead(right)
          .map { case (getFun, heap, address) => (getFun, heap, address, left) })

      readAndValue.flatMap {
        case (getFun, heap, address, value) =>
          val fields = heapInfo.objectFieldSelectors(getFun)
          indexedArrayAccess(address).flatMap { case (array, index) =>
            val arrayTerm = arrayElement(heap, array, index)
            if (fields.isEmpty) None
            else Some(fields.map { field =>
              val arrayField = context match {
                case _: PostCondition if isOldHeap(heap) =>
                  ACSLExpression.oldArrayFieldFunApp(array, index, field)
                case _ =>
                  IFunApp(field, Seq(arrayTerm))
              }
              arrayField === IFunApp(field, Seq(value))
            }.reduce(_ &&& _))
          }
      }
    }

    override def postVisit(
        t: IExpression,
        dummy: Unit,
        subres: Seq[IExpression]
    ): IExpression = {

      t match {
        // A struct-valued array read is represented as a heap-object equality.
        // Emit field equalities so ACSL consumers do not need struct equality.
        case IExpression.Eq(left: ITerm, right: ITerm) =>
          explodeIndexedStructEquality(left, right).getOrElse(t update subres)

        // get_<sort>(read(h, array-address)) ~> a[i]
        case IFunApp(
              getFun,
              Seq(
                TheoryOfHeapFunApp(
                  readFun,
                    Seq(ConstantAsProgVarProxy(h), address: ITerm)
                )
              )
            )
            if heapInfo.isObjSelector(getFun) &&
              heapInfo.isReadFun(readFun) &&
              heapInfo.isHeap(h) &&
              indexedArrayAccess(address).nonEmpty =>
          indexedArrayAccess(address) match {
            case Some((array, index)) => arrayElement(h, array, index)
            case None => t update subres
          }

        // field(get_<sort>(read(h, array-address))) ~> a[i].field
        case IFunApp(
              selector: MonoSortedIFunction,
              Seq(
                IFunApp(
                  getFun,
                  Seq(
                    TheoryOfHeapFunApp(
                      readFun,
                      Seq(ConstantAsProgVarProxy(h), address: ITerm)
                    )
                  )
                )
              )
            )
            if heapInfo.isObjSelector(getFun) &&
              heapInfo.isReadFun(readFun) &&
              isSelector(selector) &&
              heapInfo.isHeap(h) &&
              indexedArrayAccess(address).nonEmpty =>
          indexedArrayAccess(address) match {
            case Some((array, index)) =>
              IFunApp(selector, Seq(arrayElement(h, array, index)))
            case None => t update subres
          }

        case IFunApp(
              selector: MonoSortedIFunction,
              Seq(
                IFunApp(
                  getFun,
                  Seq(
                    TheoryOfHeapFunApp(
                      readFun,
                      Seq(ConstantAsProgVarProxy(h), ConstantAsProgVarProxy(p))
                    )
                  )
                )
              )
            )
            if (heapInfo.isObjSelector(getFun) &&
              heapInfo.isReadFun(readFun) &&
              isSelector(selector) &&
              heapInfo.isHeap(h)) =>
          context match {
            case _: PreCondition =>
              ACSLExpression.arrowFunApp(
                ACSLExpression.arrow,
                p,
                selector
              )
            case _: PostCondition =>
              (
                isOldHeap(h),
                p.isPreExec,
                p.isParameter
              ) match {
                case (false, false, false) =>
                  // read(@h, p), p not param => p->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrow,
                    p,
                    selector
                  )
                case (false, true, true) =>
                  // read(@h, p_0), p is param => p->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrow,
                    p,
                    selector
                  )
                case (false, true, false) =>
                  // read(@h, p_0), p not param => \old(p)->a
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.arrowOldPointer,
                    p,
                    selector
                  )
                case (true, true, true) =>
                  // read(@h_0, p_0), p is param => \old(p->a)
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.oldArrow,
                    p,
                    selector
                  )
                case (true, true, false) =>
                  // read(@h_0, p_0), p not param => \old(p->a)
                  ACSLExpression.arrowFunApp(
                    ACSLExpression.oldArrow,
                    p,
                    selector
                  )
                case _ => t update subres
              }
            // SSSOWO TODO: What about loop invariants?
            case _ => t update subres
          }

        // read(h,p).get_<sort> ~> *p
        case IFunApp(
              getFun,
              Seq(
                TheoryOfHeapFunApp(
                  readFun,
                  Seq(ConstantAsProgVarProxy(h), ConstantAsProgVarProxy(p))
                )
              )
            )
            if (heapInfo.isObjSelector(getFun) &&
              heapInfo.isReadFun(readFun) &&
              heapInfo.isHeap(h)) => {
          context match {
            case _: PreCondition =>
              ACSLExpression.derefFunApp(
                ACSLExpression.deref,
                p
              )
            case _: PostCondition =>
              (
                isOldHeap(h),
                p.isPreExec,
                p.isParameter
              ) match {
                case (false, false, false) => // read(@h, p), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.deref,
                    p
                  )
                case (false, true, true) => // read(@h, p_0), p is param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.deref,
                    p
                  )
                case (false, true, false) => // read(@h, p_0), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.derefOldPointer,
                    p
                  )
                case (true, true, true) => // read(@h_0, p_0), p is param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.oldDeref,
                    p
                  )
                case (true, true, false) => // read(@h_0, p_0), p not param
                  ACSLExpression.derefFunApp(
                    ACSLExpression.oldDeref,
                    p
                  )
                case _ => t update subres
              }
            // SSSOWO TODO: What about loop invariants?
            case _ => t update subres
          }
        }
        case _ => t update subres
      }
    }
  }
}
