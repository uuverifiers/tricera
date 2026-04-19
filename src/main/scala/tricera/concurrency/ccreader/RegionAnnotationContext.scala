/**
 * Copyright (c) 2026 Zafer Esen. All rights reserved.
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

package tricera.concurrency.ccreader

import ap.parser.{IFunction, ITerm}
import ap.parser.IExpression.Sort
import ap.theories.{Heap => HeapTheoryObject}
import ap.types.MonoSortedIFunction
import tricera.Util.SourceInfo
import tricera.acsl.ACSLTranslator
import tricera.concurrency.ccreader.CCExceptions.{NeedsHeapModelException, TranslationException}
import tricera.concurrency.heap.HeapModel

// ACSL translation context shared by function and statement contracts
class RegionAnnotationContext(tctx       : TranslationContext,
                              oldLookup  : Map[String, CCVar],
                              postLookup : Map[String, CCVar],
                              params     : scala.Seq[CCVar],
                              globals    : scala.Seq[CCVar],
                              result     : Option[CCVar],
                              srcInfo    : SourceInfo)
    extends ACSLTranslator.FunctionContext {

  def getOldVar       (ident : String) : Option[CCVar] = oldLookup.get(ident)
  def getPostGlobalVar(ident : String) : Option[CCVar] = postLookup.get(ident)
  def getParams    : scala.Seq[CCVar] = params
  def getGlobals   : scala.Seq[CCVar] = globals
  def getResultVar : Option[CCVar]    = result

  def isHeapEnabled : Boolean = tctx.modelHeap
  def getHeap : HeapTheoryObject =
    if (tctx.modelHeap) tctx.heap else throw NeedsHeapModelException

  private def acslHeap(pick : HeapModel => ITerm) : ITerm = {
    if (!tctx.modelHeap) throw NeedsHeapModelException
    try pick(tctx.heapModel.get)
    catch {
      case _ : NotImplementedError =>
        throw new TranslationException(
          "Contracts referencing the heap require a heap model that " +
          "implements ACSL pre/post state terms (currently only the " +
          "theory of heaps).")
    }
  }
  def getHeapTerm    : ITerm = acslHeap(_.getACSLPostStateHeapTerm(this))
  def getOldHeapTerm : ITerm = acslHeap(_.getACSLPreStateHeapTerm(this))

  def sortWrapper(s : Sort) : Option[IFunction] = tctx.sortWrapperMap get s
  def sortGetter (s : Sort) : Option[IFunction] = tctx.sortGetterMap  get s
  def wrapperSort(w : IFunction) : Option[Sort] = w match {
    case w : MonoSortedIFunction => tctx.wrapperSortMap.get(w)
    case _ => None
  }
  def getterSort (g : IFunction) : Option[Sort] = g match {
    case g : MonoSortedIFunction => tctx.getterSortMap.get(g)
    case _ => None
  }
  def getCtor(s : Sort) : Int = tctx.sortCtorIdMap(s)
  def getTypOfPointer(t : CCType) : CCType = t match {
    case p : CCHeapPointer => p.typ
    case _ => t
  }
  val getStructMap : Map[IFunction, CCStruct] =
    tctx.structDefs.values.map(s => (s.ctor, s)).toMap
  val annotationBeginSourceInfo : SourceInfo = srcInfo
  val annotationNumLines : Int = 1
}
