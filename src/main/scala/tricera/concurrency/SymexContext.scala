/**
 * Copyright (c) 2025 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package tricera.concurrency

import ap.parser._
import IExpression.{ConstantTerm, Predicate, Sort}
import ap.theories.Heap
import ap.types.MonoSortedIFunction
import hornconcurrency.ParametricEncoder
import lazabs.horn.bottomup.HornClauses.Clause
import tricera.Util.SourceInfo
import tricera.concurrency.CCReader._
import tricera.concurrency.ccreader._
import tricera.concurrency.concurrent_c.Absyn._
import tricera.concurrency.concurrent_c._
import tricera.properties

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

trait SymexContext {
  // --- Configuration & Global State ---
  def propertiesToCheck      : Set[properties.Property]
  def heap                   : Heap
  def printer                : PrettyPrinterNonStatic
  def atomicMode             : Boolean
  def usingInitialPredicates : Boolean
  def warnedFunctionNames    : MHashSet[String]

  // --- Data & Type Mappings ---
  def predCCPredMap     : MHashMap[Predicate, CCPredicate]
  def functionContexts  : MHashMap[String, FunctionContext]
  def functionDefs      : MHashMap[String, Absyn.Function_def]
  def functionDecls     : MHashMap[String, (Direct_declarator, CCType)]
  def structDefs        : MHashMap[String, CCStruct]
  def structInfos       : scala.Seq[StructInfo]
  def uninterpPredDecls : MHashMap[String, CCPredicate]
  def interpPredDefs    : MHashMap[String, CCTerm]
  def channels          : MHashMap[String, ParametricEncoder.CommChannel]
  def enumeratorDefs    : MHashMap[String, CCTerm]
  def sortGetterMap     : Map[Sort, MonoSortedIFunction]
  def sortWrapperMap    : Map[Sort, MonoSortedIFunction]
  def sortCtorIdMap     : Map[Sort, Int]
  def objectGetters     : scala.Seq[MonoSortedIFunction]
  def defObj            : IFunction

  // --- Clause & Predicate Generation ---
  def output(c    : CCClause,
             sync : ParametricEncoder.Synchronisation = ParametricEncoder.NoSync) : Unit
  def addAssertion(assertion : CCAssertionClause) : Unit
  def newPred(extraArgs : scala.Seq[CCVar],
              srcInfo   : Option[SourceInfo]) : CCPredicate
  def newPred(name : String,
              args : scala.Seq[CCVar],
              srcInfo : Option[SourceInfo]) : CCPredicate
  def getRichClause(c : Clause) : Option[CCClause]
  def addRichClause(c : Clause, srcInfo : Option[SourceInfo]) : CCClause
  def mkRichAssertionClause(c       : Clause,
                            srcInfo : Option[SourceInfo],
                            p       : properties.Property) : CCAssertionClause
  def atom(p : CCPredicate, a       : scala.Seq[ITerm]) : IAtom
  def atom(p : CCPredicate) : IAtom

  // --- Control Flow & Inlining ---
  def inAtomicMode[A](comp : => A) : A
  def mergeClauses(from : Int) : Unit
  def clausesSize : Int
  def inlineFunction(f          : Function_def,
                     entry      : CCPredicate,
                     exit       : CCPredicate,
                     args       : List[CCType],
                     isNoReturn : Boolean,
                     fName      : String) : Unit
  def isTermUsedInClauses(term : ConstantTerm) : Boolean

  // --- Helpers ---
  def getType(d   : Function_def)   : CCType
  def getType(s   : Type_specifier) : CCType
  def getType(tn  : Type_name)      : CCType
  def getType(exp : Ebytestype)     : CCType
  def getFunctionArgNames(f : Function_def) : scala.Seq[String]

  def translateClockValue   (value : CCTerm) : CCTerm
  def translateDurationValue(value : CCTerm) : CCTerm
}
