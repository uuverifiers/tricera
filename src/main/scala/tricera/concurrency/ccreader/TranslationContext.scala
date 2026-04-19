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

import ap.parser.{IAtom, ITerm}
import ap.parser.IExpression.Sort
import ap.theories.{Heap => HeapTheoryObject}
import ap.types.MonoSortedIFunction
import hornconcurrency.ParametricEncoder
import lazabs.horn.bottomup.HornClauses.Clause
import tricera.Util.SourceInfo
import tricera.acsl.FunctionContract
import tricera.concurrency.CCReader.{CCAssertionClause, CCClause}
import tricera.concurrency.heap.HeapModel
import tricera.properties

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

trait TranslationContext {
  def scope       : CCScope
  def modelHeap   : Boolean
  def heap        : HeapTheoryObject
  def heapModel   : Option[HeapModel]
  def heapVars    : Map[String, CCVar]

  def clauses          : ArrayBuffer[(Clause, ParametricEncoder.Synchronisation)]
  def assertionClauses : ArrayBuffer[CCAssertionClause]

  def output           (c : CCClause,
                        sync : ParametricEncoder.Synchronisation =
                          ParametricEncoder.NoSync) : Unit
  def addRichClause    (clause : Clause,
                        srcInfo : Option[SourceInfo]) : CCClause
  def mkRichAssertionClause(clause  : Clause,
                            srcInfo  : Option[SourceInfo],
                            property : properties.Property) : CCAssertionClause

  def functionClauses
    : MHashMap[String, scala.Seq[(Clause, ParametricEncoder.Synchronisation)]]
  def functionAssertionClauses
    : MHashMap[String, scala.Seq[CCAssertionClause]]

  def newPred(args : scala.Seq[CCVar],
              srcInfo : Option[SourceInfo]) : CCPredicate
  def newPred(name : String,
              args : scala.Seq[CCVar],
              srcInfo : Option[SourceInfo]) : CCPredicate
  def atom(p : CCPredicate, args : scala.Seq[ITerm]) : IAtom
  def atom(p : CCPredicate) : IAtom

  def contracts : MHashMap[String, ContractRegistration]
  def registerStatementContract(
      name            : String,
      prePred         : CCPredicate,
      postPred        : CCPredicate,
      contract        : Option[FunctionContract],
      isUserAnnotated : Boolean,
      returnVariant   : Option[ContractRegistration],
      srcInfo         : Option[SourceInfo]) : ContractRegistration

  def functionPostOldArgs : MHashMap[String, scala.Seq[CCVar]]

  def sortWrapperMap : Map[Sort, MonoSortedIFunction]
  def sortGetterMap  : Map[Sort, MonoSortedIFunction]
  def wrapperSortMap : Map[MonoSortedIFunction, Sort]
  def getterSortMap  : Map[MonoSortedIFunction, Sort]
  def sortCtorIdMap  : Map[Sort, Int]
  def structDefs     : MHashMap[String, CCStruct]
}
