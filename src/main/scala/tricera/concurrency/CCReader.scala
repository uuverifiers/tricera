/**
 * Copyright (c) 2015-2025 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.{ADT, ExtArray}
import ap.theories.heaps._
import ap.types.{MonoSortedIFunction, MonoSortedPredicate}
import ap.util.Seqs.reduceToSize
import concurrent_c._
import concurrent_c.Absyn._
import hornconcurrency.ParametricEncoder
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.abstractions.VerificationHints._
import lazabs.horn.bottomup.HornClauses
import IExpression.{ConstantTerm, Predicate, Sort, toFunApplier}

import scala.collection.mutable.{ArrayBuffer, Stack, HashMap => MHashMap,
  HashSet => MHashSet}
import tricera.Util._
import tricera.acsl.{ACSLTranslator, FunctionContract}
import tricera.concurrency.ccreader._
import tricera.HeapInfo
import tricera.params.TriCeraParameters
import tricera.parsers.AnnotationParser
import tricera.parsers.AnnotationParser._
import CCExceptions._
import tricera.{Util, properties}
import tricera.Literals
import tricera.concurrency.heap.{HeapModel, HeapModelFactory, HeapTheoryModel}

/** Implicit conversion so that we can get a Scala-like iterator from a
 * a Java list */
import scala.jdk.CollectionConverters._
import ap.util.Debug
import scala.collection.immutable.HashMap
import scala.collection.mutable

object CCReader {
  private[concurrency] var useTime = false
  private[concurrency] var modelHeap = false

  // Reserve two variables for time
  private[concurrency] val GT  = new CCVar("_GT", None, CCClock, GlobalStorage)
  private[concurrency] val GTU = new CCVar("_GTU", None, CCInt, GlobalStorage)

  def apply(input : java.io.Reader, entryFunction : String,
            propertiesToCheck : Set[properties.Property] = Set(
              properties.Reachability))
  : (CCReader, Boolean, CallSiteTransform.CallSiteTransforms) = { // second ret. arg is true if modelled heap
    def entry(parser : concurrent_c.parser) = parser.pProgram
    val prog = parseWithEntry(input, entry _)
    val atCallTransformedProg = CCAstAtExpressionTransformer.transform(prog)
    val typeAnnotProg = CCAstTypeAnnotator(atCallTransformedProg)
    val (transformedCallsProg, callSiteTransforms) =
      CCAstStackPtrArgToGlobalTransformer(typeAnnotProg, entryFunction)
  
    var reader : CCReader = null
    while (reader == null)
      try {
        reader = new CCReader(
          transformedCallsProg, entryFunction, propertiesToCheck, scala.Seq())
      } catch {
        case NeedsTimeException => {
          warn("enabling time")
          useTime = true
        }
        case NeedsHeapModelException => {
          modelHeap = true
        }
      }
    (reader, modelHeap, callSiteTransforms)
  }

  /**
   * Parse starting at an arbitrarily specified entry point
   */
  private[concurrency] def parseWithEntry[T](input : java.io.Reader,
                                             entry : (parser) => T) : T = {
    val l = new Yylex(new ap.parser.Parser2InputAbsy.CRRemover2 (input))
    val p = new parser(l, l.getSymbolFactory())

    try { entry(p) } catch {
      case e : Exception =>
        Util.warn(
"""The input program could not be parsed. If 'main' is not the entry point to
   |the program, use the option '-m:entry-function-name' to specify the entry point.""".stripMargin)
        throw new ParseException(
             "At line " + String.valueOf(l.line_num()) +
             ", near \"" + l.buff() + "\" :" +
             "     " + e.getMessage())
    } finally {
      input.close
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  object ArithmeticMode extends Enumeration {
    val Mathematical, ILP32, LP64, LLP64 = Value
  }
  //////////////////////////////////////////////////////////////////////////////
  class CCClause(val clause  : HornClauses.Clause,
                 val srcInfo : Option[SourceInfo]) {
    override def toString : String =
      clause.toPrologString + (srcInfo match {
        case None => ""
        case Some(SourceInfo(line, col)) =>
          s" (line:$line col:$col)"
      })
  }
  object CCClause {
    def unapply(clause : CCClause)
    : Option[(HornClauses.Clause, Option[SourceInfo])] =
      Some((clause.clause, clause.srcInfo))
  }

  class CCAssertionClause(clause   : HornClauses.Clause,
                          srcInfo  : Option[SourceInfo],
                          val property : properties.Property)
  extends CCClause(clause, srcInfo) {
    override def toString : String =
      super.toString + s" (property: $property)"
  }

  class FunctionContext (val prePred  : CCPredicate,
                         val postPred : CCPredicate,
                         val acslContext : ACSLTranslator.FunctionContext,
                         val prePredACSLArgNames : scala.Seq[String],
                         val postPredACSLArgNames : scala.Seq[String],
                         val heapModel : Option[HeapModel])

  case class FuncDef(body : Compound_stm,
                     decl : Declarator,
                     sourceInfo : SourceInfo,
                     declSpecs : Option[ListDeclaration_specifier] = None,
                     annotations : scala.Seq[Annotation]) {
    val name : String = getName(decl)
  }

  object FuncDef {
    def apply(funDef : Function_def) : FuncDef = {
      funDef match {
        case f : NewFunc =>
          FuncDef(f.compound_stm_, f.declarator_,
                  getSourceInfo(f),
                  Some(f.listdeclaration_specifier_),
                  Nil)
        case f : NewFuncInt =>
          FuncDef(f.compound_stm_, f.declarator_,
                  getSourceInfo(f), None,
                  f.listannotation_.asScala.toSeq)
        case f : AnnotatedFunc =>
          FuncDef(f.compound_stm_, f.declarator_,
                  getSourceInfo(f),
                  Some(f.listdeclaration_specifier_),
                  f.listannotation_.asScala.toSeq)
      }
    }
  }

  def getName (f : Function_def) : String = getName(FuncDef(f).decl)
  def getName (t : Thread_def) : String = t match {
    case decl : SingleThread => decl.cident_
    case decl : ParaThread => decl.cident_2
  }

  def getName(decl : Declarator) : String = decl match {
    case decl : NoPointer => getName(decl.direct_declarator_)
    case decl : BeginPointer => getName(decl.direct_declarator_)
  }

  def getName(decl : Direct_declarator) : String = decl match {
    case decl : Name      => decl.cident_
    case decl : ParenDecl => getName(decl.declarator_)
    case dec : NewFuncDec => getName(dec.direct_declarator_)
//    case dec : OldFuncDef => getName(dec.direct_declarator_)
    case dec : OldFuncDec => getName(dec.direct_declarator_)
    case dec : InitArray => getName(dec.direct_declarator_)
    case dec : Incomplete => getName(dec.direct_declarator_)
    case dec : MathArray => getName(dec.direct_declarator_)
  }
}

////////////////////////////////////////////////////////////////////////////////

class CCReader private (prog              : Program,
                        entryFunction     : String,
                        propertiesToCheck : Set[properties.Property],
                        inputVarNames     : scala.Seq[String]) {

  import CCReader._

  private val printer = new PrettyPrinterNonStatic

  private val scope = new CCScope()

  private val symexContext : SymexContext = new SymexContext {
    // --- Configuration & Global State ---
    override def propertiesToCheck : Set[properties.Property] =
      CCReader.this.propertiesToCheck
    override def heap : Heap =
      CCReader.this.heap
    override def printer : PrettyPrinterNonStatic =
      CCReader.this.printer
    override def atomicMode : Boolean =
      CCReader.this.atomicMode
    override def usingInitialPredicates : Boolean =
      CCReader.this.usingInitialPredicates
    override def warnedFunctionNames : MHashSet[String] =
      CCReader.this.warnedFunctionNames

    // --- Data & Type Mappings ---
    override def predCCPredMap : MHashMap[Predicate, CCPredicate] =
      CCReader.this.predCCPredMap
    override def functionContexts : MHashMap[String, FunctionContext] =
      CCReader.this.functionContexts
    override def functionDefs : MHashMap[String, Absyn.Function_def] =
      CCReader.this.functionDefs
    override def functionDecls : MHashMap[String, (Direct_declarator, CCType)] =
      CCReader.this.functionDecls
    override def structDefs : MHashMap[String, CCStruct] =
      CCReader.this.structDefs
    override def structInfos : scala.Seq[StructInfo] =
      CCReader.this.structInfos.toSeq
    override def uninterpPredDecls : MHashMap[String, CCPredicate] =
      CCReader.this.uninterpPredDecls
    override def interpPredDefs : MHashMap[String, CCTerm] =
      CCReader.this.interpPredDefs
    override def channels : MHashMap[String, ParametricEncoder.CommChannel] =
      CCReader.this.channels
    override def enumeratorDefs : MHashMap[String, CCTerm] =
      CCReader.this.enumeratorDefs
    override def sortGetterMap : Map[Sort, MonoSortedIFunction] =
      CCReader.this.sortGetterMap
    override def sortWrapperMap : Map[Sort, MonoSortedIFunction] =
      CCReader.this.sortWrapperMap
    override def sortCtorIdMap : Map[Sort, Int] =
      CCReader.this.sortCtorIdMap
    override def objectGetters : scala.Seq[MonoSortedIFunction] =
      CCReader.this.objectGetters
    override def defObj : IFunction =
      CCReader.this.defObj

    // --- Clause & Predicate Generation ---
    override def output(c : CCClause,
                        sync : ParametricEncoder.Synchronisation
                          = ParametricEncoder.NoSync) : Unit =
      CCReader.this.output(c, sync)
    override def addAssertion(assertion : CCAssertionClause) : Unit =
      CCReader.this.assertionClauses += assertion
    override def newPred(extraArgs : scala.Seq[CCVar],
                         srcInfo : Option[SourceInfo]) : CCPredicate =
      CCReader.this.newPred(extraArgs, srcInfo)
    override def newPred(name : String, args : scala.Seq[CCVar],
                         srcInfo : Option[SourceInfo]) : CCPredicate =
      CCReader.this.newPred(name, args, srcInfo)
    override def atom(p : CCPredicate, a : scala.Seq[ITerm]): IAtom =
      CCReader.this.atom(p, a)
    override def atom(p : CCPredicate) : IAtom =
      CCReader.this.atom(p)
    override def getRichClause(c : HornClauses.Clause) : Option[CCClause] =
      CCReader.this.getRichClause(c)
    override def addRichClause(c : HornClauses.Clause,
                               srcInfo : Option[SourceInfo]) : CCClause =
      CCReader.this.addRichClause(c, srcInfo)
    override def mkRichAssertionClause(c : HornClauses.Clause,
                                       srcInfo : Option[SourceInfo],
                                       p : properties.Property) : CCAssertionClause =
      CCReader.this.mkRichAssertionClause(c, srcInfo, p)

    // --- Control Flow & Inlining ---
    override def inAtomicMode[A](comp : => A): A =
      CCReader.this.inAtomicMode(comp)
    override def mergeClauses(from : Int) : Unit =
      CCReader.this.mergeClauses(from)
    override def clausesSize : Int =
      CCReader.this.clauses.size
    override def inlineFunction(f          : Function_def,
                                entry      : CCPredicate,
                                exit       : CCPredicate,
                                args       : List[CCType],
                                isNoReturn : Boolean,
                                fName      : String) : Unit =
      CCReader.this.inlineFunction(f, entry, exit, args, isNoReturn, fName)
    override def isTermUsedInClauses(term : ConstantTerm) : Boolean = {
      if (clauses.exists(_._1 == null)) return true // can happen in jump stmts
      (assertionClauses.iterator.flatMap(_.clause.constants) ++
       clauses.iterator.flatMap(_._1.constants)).toSet.contains(term)
    }

    // --- Helpers ---
    override def getType(d : Function_def) : CCType =
      CCReader.this.getType(d)
    override def getType(s : Type_specifier) : CCType =
      CCReader.this.getType(s)
    override def getType(tn : Type_name) : CCType =
      CCReader.this.getType(tn)
    override def getType(exp : Ebytestype) : CCType =
      CCReader.this.getType(exp)
    override def getFunctionArgNames(f : Function_def) : scala.Seq[String] =
      CCReader.this.getFunctionArgNames(f)
    override def translateClockValue(expr : CCTerm) : CCTerm =
      CCReader.this.translateClockValue(expr)
    override def translateDurationValue(expr : CCTerm): CCTerm =
      CCReader.this.translateDurationValue(expr)
  }

  //////////////////////////////////////////////////////////////////////////////

  import HornClauses.Clause

  private val predCCPredMap = new MHashMap[Predicate, CCPredicate]

  private var globalPreconditions : IFormula = true

  private var usingInitialPredicates = false

  //////////////////////////////////////////////////////////////////////////////

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  private val functionDefs  = new MHashMap[String, Function_def]
  private val functionDecls = new MHashMap[String, (Direct_declarator, CCType)]
  private val warnedFunctionNames = new MHashSet[String]
  private val functionContexts = new MHashMap[String, FunctionContext]
  private val functionPostOldArgs = new MHashMap[String, scala.Seq[CCVar]]
  private val functionClauses =
    new MHashMap[String, scala.Seq[(Clause, ParametricEncoder.Synchronisation)]]
  private val functionAssertionClauses = new MHashMap[String, scala.Seq[CCAssertionClause]]
  private val uniqueStructs = new MHashMap[Unique, String]
  private val structInfos   = new ArrayBuffer[StructInfo]
  private val structDefs    = new MHashMap[String, CCStruct]
  private val enumDefs      = new MHashMap[String, CCType]
  private val enumeratorDefs= new MHashMap[String, CCTerm]

  private val uninterpPredDecls     = new MHashMap[String, CCPredicate]
  private val interpPredDefs        = new MHashMap[String, CCTerm]
  private val loopInvariants        =
    new MHashMap[String, (CCPredicate, SourceInfo)]

  def getLoopInvariants = loopInvariants.toMap
  def getFunctionContexts = functionContexts.toMap

  // NOTE: Used by ACSL encoder.
  var hasACSLEntryFunction : Boolean = false
  val funToPreAtom  : MHashMap[String, IAtom] = new MHashMap()
  val funToPostAtom : MHashMap[String, IAtom] = new MHashMap()
  val funToContract : MHashMap[String, FunctionContract] = new MHashMap()
  val funsWithAnnot : MHashSet[String] = new MHashSet()
  val prePredsToReplace : MHashSet[Predicate] = new MHashSet()
  val postPredsToReplace : MHashSet[Predicate] = new MHashSet()
  val clauseToRichClause : MHashMap[Clause, CCClause] = new MHashMap()

  //////////////////////////////////////////////////////////////////////////////

  private[tricera]
  def addRichClause(clause  : Clause,
                    srcInfo : Option[SourceInfo]) : CCClause = {
    val richClause = new CCClause(clause, srcInfo)
    clauseToRichClause += clause -> richClause
    richClause
  }

  private[tricera]
  def mkRichAssertionClause(clause       : Clause,
                            srcInfo      : Option[SourceInfo],
                            propertyType : properties.Property)
  : CCAssertionClause = {
    val richClause = new CCAssertionClause(clause, srcInfo, propertyType)
    clauseToRichClause += clause -> richClause
    richClause
  }

  //////////////////////////////////////////////////////////////////////////////

  private val processes =
    new ArrayBuffer[(ParametricEncoder.Process, ParametricEncoder.Replication)]

  private val assertionClauses = new ArrayBuffer[CCAssertionClause]
  private val timeInvariants = new ArrayBuffer[Clause]

  private val clauses =
    new ArrayBuffer[(Clause, ParametricEncoder.Synchronisation)]

  private def output(c : CCClause,
                     sync : ParametricEncoder.Synchronisation =
                       ParametricEncoder.NoSync) : Unit = {
    clauses += ((c.clause, sync))
  }

  import ParametricEncoder.merge

  private def mergeClauses(from : Int) : Unit = if (from < clauses.size - 1) {
    val concernedClauses = clauses.slice(from, clauses.size)
    val (entryClauses, transitionClauses) =
      if (concernedClauses.head._1.body.isEmpty) {
        concernedClauses partition (_._1.body.isEmpty)
      } else {
        val entryPred = concernedClauses.head._1.body.head.pred
        concernedClauses partition (_._1.body.head.pred == entryPred)
      }
    val lastClauses = transitionClauses groupBy (_._1.body.head.pred)

    reduceToSize(clauses, from)

    def chainClauses(currentClause : CCClause,
                     currentSync : ParametricEncoder.Synchronisation,
                     seenPreds : Set[Predicate]) : Unit =
      if (!currentClause.clause.hasUnsatConstraint) {
        val headPred = currentClause.clause.head.pred
        if (seenPreds contains headPred)
          throw new TranslationException(
            "cycles in atomic blocks are not supported yet")

        (lastClauses get headPred) match {
          case Some(cls) => {
            if (timeInvariants exists (_.predicates contains headPred))
              throw new TranslationException(
                "time invariants in atomic blocks are not supported")

            for ((c, sync) <- cls)
              if (currentSync == ParametricEncoder.NoSync)
                chainClauses(addRichClause( // todo: use currentClause srcInfo?
                  merge(c, currentClause.clause), currentClause.srcInfo), sync,
                             seenPreds + headPred)
              else if (sync == ParametricEncoder.NoSync)
                chainClauses(addRichClause(
                  merge(c, currentClause.clause), currentClause.srcInfo), currentSync,
                             seenPreds + headPred)
              else
                throw new TranslationException(
                  "Cannot execute " + currentSync + " and " + sync +
                  " in one step")

            // add further assertion clauses, since some intermediate
            // states disappear
            for (c <- assertionClauses.toList)
              if (c.clause.bodyPredicates contains headPred) {
                if (currentSync != ParametricEncoder.NoSync)
                  throw new TranslationException(
                    "Cannot execute " + currentSync + " and an assertion" +
                    " in one step")
                val newAssertionClause = merge(c.clause, currentClause.clause)
                if (!newAssertionClause.hasUnsatConstraint)
                  assertionClauses += mkRichAssertionClause(
                    newAssertionClause, c.srcInfo, c.property)
              }
          }
          case None =>
            clauses += ((currentClause.clause, currentSync))
        }
      }

    for ((c, sync) <- entryClauses)
      chainClauses(getRichClause(c).get, sync, Set())
  }

  private var atomicMode = false

  private def inAtomicMode[A](comp : => A) : A = {
      val oldAtomicMode = atomicMode
      atomicMode = true
      val res = comp
      atomicMode = oldAtomicMode
      res
  }

  private var prefix : String = ""
  private var locationCounter = 0

  private def setPrefix(pref : String) = {
    prefix = pref
    locationCounter = 0
  }

  def addLoopInvariant(pred : CCPredicate, srcInfo : SourceInfo) : Unit = {
    loopInvariants += ((pred.pred.name, (pred, srcInfo)))
  }

  def newPred(name : String,
              args : scala.Seq[CCVar],
              srcInfo : Option[SourceInfo]) : CCPredicate = {
    val pred = MonoSortedPredicate(name, args map (_ sort))
    val ccPred = CCPredicate(pred, args, srcInfo)
    predCCPredMap.put(pred, ccPred)
    ccPred
  }

  private def newPred(extraArgs : scala.Seq[CCVar],
                      srcInfo : Option[SourceInfo]) : CCPredicate = {
    val predNameSuffix = srcInfo match {
      case Some(SourceInfo(line, col)) => s"${line}_$col"
      case None => ""
    }
    val predName =
      if (predicateHints.exists(_._1.name == prefix + predNameSuffix)) {
        val s = prefix + predNameSuffix + "_" + locationCounter
        locationCounter = locationCounter + 1
        s
      } else prefix + predNameSuffix
    val res = newPred(predName, scope.allFormalVars ++ extraArgs, srcInfo)

    val hints = for (s <- scope.variableHints; p <- s) yield p
    val allHints =
      if (hints exists (_.isInstanceOf[VerifHintTplElement])) {
        // make sure that all individual variables exist as templates
        val coveredVars =
          (for (VerifHintTplEqTerm(IVariable(n), _) <- hints.iterator)
           yield n).toSet
        hints ++ (for (n <- (0 until res.arity).iterator;
                       if (!(coveredVars contains n)))
                  yield VerifHintTplEqTerm(IExpression.v(n), 10000))
      } else {
        hints
      }

    predicateHints.put(res.pred, allHints.toSeq)
    res
  }

  private val predicateHints =
    new MHashMap[Predicate, scala.Seq[VerifHintElement]]

  //////////////////////////////////////////////////////////////////////////////

  if (useTime) {
    scope.GlobalVars addVar GT
    scope.GlobalVars.inits += CCTerm.fromTerm(GT.term, CCClock, None)
    scope.GlobalVars addVar GTU
    scope.GlobalVars.inits += CCTerm.fromTerm(GTU.term, CCInt, None)
    scope.variableHints += List()
    scope.variableHints += List()
  }

  private def collectStructDefsFromComp (comp : Compound_stm): Unit = {
    comp match {
      case        _: ScompOne =>
      case compound: ScompTwo =>
        val stmsIt = ap.util.PeekIterator(compound.liststm_.asScala.iterator)
        while (stmsIt.hasNext) stmsIt.next match {
          case dec: DecS => collectStructDefs(dec.dec_)
          case _ =>
        }
    }
  }

  implicit def annotationStringExtractor(annot : Annotation) : String = {
    val str = annot match {
      case a : Annot1 => a.annotationstring_
    }
    str.substring(2, str.length-2) // removes the annotation markers
  }

  for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_.asScala)
    decl match {
      case decl: Global => collectStructDefs(decl.dec_)
      case fun: Afunc =>
        val comp = FuncDef(fun.function_def_).body
        collectStructDefsFromComp(comp)
      case thread : Athread =>
        val comp = thread.thread_def_ match {
          case t : SingleThread => t.compound_stm_
          case t : ParaThread => t.compound_stm_
        }
        collectStructDefsFromComp(comp)
      case _ =>
    }

  import ap.theories.{Heap => HeapObj}

  def defObjCtor(objectCtors : scala.Seq[IFunction]) : ITerm = objectCtors.last()
  val ObjSort = HeapObj.ADTSort(0)

  val structCtorSignatures : List[(String, HeapObj.CtorSignature)] =
    (for ((struct, i) <- structInfos zipWithIndex) yield {
      if(struct.fieldInfos isEmpty) warn(
        s"Struct ${struct.name} was declared, but never defined, " +
          "or it has no fields.")
      val ADTFieldList : scala.Seq[(String, HeapObj.CtorArgSort)] =
        for(FieldInfo(rawFieldName, fieldType, ptrDepth) <-
              struct.fieldInfos) yield
          (CCStruct.rawToFullFieldName(struct.name, rawFieldName),
            if (ptrDepth > 0) Heap.AddrSort
            else { fieldType match {
              case Left(ind) => HeapObj.ADTSort(ind + 1)
              case Right(typ) =>
                typ match {
                  case _ : CCHeapArrayPointer => HeapObj.AddrRangeSort
                  case _ => HeapObj.OtherSort(typ.toSort)
                }
            }
            })
      (struct.name, HeapObj.CtorSignature(ADTFieldList, HeapObj.ADTSort(i+1)))
    }).toList

  // todo: only add types that exist in the program - should also add machine arithmetic types
  val predefSignatures =
    List(("O_Int", HeapObj.CtorSignature(List(("getInt", HeapObj.OtherSort(Sort.Integer))), ObjSort)),
         ("O_UInt", HeapObj.CtorSignature(List(("getUInt", HeapObj.OtherSort(Sort.Nat))), ObjSort)),
         ("O_Addr", HeapObj.CtorSignature(List(("getAddr", HeapObj.AddrSort)), ObjSort)),
         ("O_AddrRange", HeapObj.CtorSignature(List(("getAddrRange", HeapObj.AddrRangeSort)), ObjSort))
    )

  val wrapperSignatures : List[(String, HeapObj.CtorSignature)] =
    predefSignatures ++
      (for ((name, signature) <- structCtorSignatures) yield {
        ("O_" + name,
          HeapObj.CtorSignature(List(("get" + name, signature.result)), ObjSort))
      })

  // TODO: use ADT/Heap depending on HeapModel, and move heap theory declaration
  //       to HeapModel.
  val heap = TriCeraParameters.get.heapModel match {
    case TriCeraParameters.NativeHeap =>
      new NativeHeap("Heap", "Addr", "AddrRange", ObjSort,
                     List("HeapObject") ++ structCtorSignatures.unzip._1,
                     wrapperSignatures ++ structCtorSignatures ++
                     List(("defObj", HeapObj.CtorSignature(List(), ObjSort))),
                     defObjCtor)
    case TriCeraParameters.ArrayHeap =>
      new ArrayHeap("Heap", "Addr", "AddrRange", ObjSort,
                    List("HeapObject") ++ structCtorSignatures.unzip._1,
                    wrapperSignatures ++ structCtorSignatures ++
                    List(("defObj", HeapObj.CtorSignature(List(), ObjSort))),
                    defObjCtor)
  }

  def getHeapInfo = if (modelHeap) Some(HeapInfo(heap, heapModel.get)) else None

  private val structCtorsOffset = predefSignatures.size
  val defObj = heap.userHeapConstructors.last
  val structCount = structInfos.size
  val objectWrappers = heap.userHeapConstructors.take(structCount+structCtorsOffset)
  val objectGetters =
    for (sels <- heap.userHeapSelectors.take(structCount+structCtorsOffset)
         if sels.nonEmpty) yield sels.head
  val structCtors = heap.userHeapConstructors.slice(structCtorsOffset+structCount,
    structCtorsOffset+2*structCount)
  val structSels = heap.userHeapSelectors.slice(structCtorsOffset+structCount,
    structCtorsOffset+2*structCount)

  val objectSorts : scala.IndexedSeq[Sort] = objectGetters.toIndexedSeq.map(f => f.resSort)
  val sortGetterMap : Map[Sort, MonoSortedIFunction] =
    objectSorts.zip(objectGetters).toMap
  val sortWrapperMap : Map[Sort, MonoSortedIFunction] =
    objectSorts.zip(objectWrappers).toMap
  val getterSortMap : Map[MonoSortedIFunction, Sort] =
    sortGetterMap.map(_.swap)
  val wrapperSortMap : Map[MonoSortedIFunction, Sort] =
    sortWrapperMap.map(_.swap)
  val sortCtorIdMap : Map[Sort, Int] =
    objectSorts.zip(0 until structCount+structCtorsOffset).toMap

  for (((ctor, sels), i) <- structCtors zip structSels zipWithIndex) {
    val curStruct = structInfos(i)
    val fieldInfos = curStruct.fieldInfos
    val fieldsWithType = for (j <- fieldInfos.indices) yield {
      val fullFieldName =
        CCStruct.rawToFullFieldName(curStruct.name, fieldInfos(j).name)
      assert(sels(j).name == fullFieldName)
      (sels(j),{
        val actualType = fieldInfos(j).typ match {
        case Left(ind) => CCStructField(structInfos(ind).name, structDefs)
        case Right(typ) =>
          typ match {
            case t : CCHeapArrayPointer => // replace with initialized heap
              CCHeapArrayPointer(heap, t.elementType, t.arrayLocation) // todo: would fail for arrays of arrays inside structs
            case _ => typ
          }
      }
      if(fieldInfos(j).ptrDepth > 0) CCHeapPointer(heap, actualType)
      else actualType})}
    structDefs += ((ctor.name, CCStruct(ctor, fieldsWithType)))
  }

  private val globalVars : scala.Seq[CCVarDeclaration] =
    if (inputVarNames.nonEmpty) {
      for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_.asScala
           if decl.isInstanceOf[Global]) yield
        collectVarDecls(decl.asInstanceOf[Global].dec_, true)
    }.flatten.filter(_.isInstanceOf[CCVarDeclaration])
     .map(_.asInstanceOf[CCVarDeclaration]).toSeq
    else scala.Seq()
  private val inputVars : scala.Seq[CCVar] = inputVarNames.map { name =>
    globalVars.find(_.name == name) match {
      case Some(v) => new CCVar(v.name, Some(v.srcInfo), v.typ, GlobalStorage)
      case None => throw new TranslationException(
        s"INPUT variable '$name' from comment is not declared as a global variable.")
    }
  }

  private val heapModelFactory : HeapModelFactory =
    HeapModel.factory(HeapModel.ModelType.TheoryOfHeaps, symexContext, scope, inputVars)

  for ((name, funcDefAst) <- heapModelFactory.getFunctionsToInject if modelHeap) {
    if (functionDefs.contains(name)) {
      throw new TranslationException(
        s"Heap model function '$name' clashes with an existing function.")
    }
    functionDefs.put(name, funcDefAst)
  }

  private val heapVars : Map[String, CCVar] = if (modelHeap) {
    (for (v <- heapModelFactory.requiredVars) yield {
      val newVar =
        new CCVar(v.name, None, v.typ, if (v.isGlobal) GlobalStorage else AutoStorage)
      if (v.isGlobal) {
        scope.GlobalVars.addVar(newVar)
        scope.GlobalVars.inits += CCTerm.fromTerm(v.initialValue, v.typ, None)
        scope.variableHints += List() // Add placeholder for hints
      } else { // For thread-local variables, if any model needs them
        scope.LocalVars.addVar(newVar)
      }
      v.name -> newVar
    }).toMap } else Map.empty

  private val heapPreds : Map[String, CCPredicate] = if(modelHeap) {
    (for (pred <- heapModelFactory.requiredPreds) yield {
      val newPred   = this.newPred(pred.name, pred.args, None)
      uninterpPredDecls += pred.name -> newPred
      pred.name -> newPred
    }).toMap
  } else Map.empty

  private val heapModel : Option[HeapModel] =
    if(modelHeap)
      Some(heapModelFactory(HeapModel.Resources(heapVars, heapPreds)))
    else None

  /**
   * It is important that globalExitPred has arguments for any variables
   * needed by the heap model - for instance we want to check that memory is
   * cleaned before exit, and it cannot be done if the variable tracking memory
   * does not exist at that point.
   * This exit predicate is reached, for instance, with the `abort` statement.
   */
  private val globalExitPred = newPred("exit", scope.allFormalVars, None)

  //////////////////////////////////////////////////////////////////////////////
  private def translateProgram : Unit = {
    // First collect all declarations. This is a bit more
    // generous than actual C semantics, where declarations
    // have to be in the right order
    import IExpression._
    import tricera.Literals

    atomicMode = true
    val values = Symex(symexContext, scope, null, heapModel)

    /**
     * Collect global variables and their initializers.
     */
    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_.asScala)
      decl match {
        case decl : Global =>
          collectVarDecls(decl.dec_, true, values, "", false)

        case decl : Chan =>
          for (name <- decl.chan_def_.asInstanceOf[AChan].listcident_.asScala) {
            if (channels contains name)
              throw new TranslationException(
                "Channel " + name + " is already declared")
            channels.put(name, new ParametricEncoder.CommChannel(name))
          }

        case decl : Afunc => {
          val name = getName(decl.function_def_)

          if (functionDefs contains name)
            throw new TranslationException(
              "Function " + name + " is already declared")
          functionDefs.put(name, decl.function_def_)
        }

        case _ => // nothing
      }

    val globalsSize = scope.GlobalVars.size
    /**
     * Collect static variables and their initializers.
     * Static variables can appear only at the outermost scope of function
     * declarations.
     */
    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_.asScala) {
      val funNameAndBody : Option[(String, Compound_stm)] = decl match {
        case decl : Afunc =>
          val funcDef = FuncDef(decl.function_def_)
          Some(funcDef.name, funcDef.body)
        case decl : Athread =>
          val name = getName(decl.thread_def_)
          val body = decl.thread_def_ match {
            case d : SingleThread => d.compound_stm_
            case d : ParaThread   => d.compound_stm_
          }
          Some(name, body)
        case _ => None
      }
      funNameAndBody match {
        case Some((name ,body)) =>
          val decs = body match {
            case _ : ScompOne     => Nil
            case stmts : ScompTwo =>
              stmts.liststm_.asScala.filter(_.isInstanceOf[DecS])
                                    .map(_.asInstanceOf[DecS])
          }
          assert(name nonEmpty, "Empty function name before collecting its static variables.")
          decs.foreach(dec => collectVarDecls(dec.dec_, false, values, name, true))
        case None => // nothing needed
      }
    }

    assert(scope.GlobalVars.vars.drop(globalsSize).forall(v => v.isStatic),
           "Non-static variables added while looking for static variables!")

    // prevent time variables, heap variable, and global ghost variables
    // from being initialised twice
    // TODO: This is very brittle and unintuitive - come up with a better solution.
    scope.GlobalVars.inits ++= (values.getValues drop
      heapVars.size + (if (useTime) 2 else 0))
    // if while adding glboal variables we have changed the heap variables,
    // they need to be reinitialised as well.
    // Happens with global array allocations for instance.
    if (modelHeap) {
      for((_, heapVar) <- heapVars) {
        val varInd = scope.GlobalVars.lastIndexWhere(heapVar)
        val maybeNewInitVal = values.getValues(varInd)
        val originalInitVal = IConstant(scope.GlobalVars.vars(varInd).term)
        if (modelHeap && maybeNewInitVal.toTerm != originalInitVal) {
          scope.GlobalVars.inits(varInd) = maybeNewInitVal
        }
      }
    }

    globalPreconditions = globalPreconditions &&& values.getGuard

    // todo: what about functions without definitions? replace Afunc type
    val functionAnnotations : Map[Afunc, scala.Seq[(AnnotationInfo, SourceInfo)]] =
      prog.asInstanceOf[Progr].listexternal_declaration_.asScala.collect {
        case f : Afunc  =>
          val annots : scala.Seq[Annotation] = f.function_def_ match {
            case f: AnnotatedFunc => f.listannotation_.asScala.toList
            case f: NewFuncInt    => f.listannotation_.asScala.toList
            case _: NewFunc       => Nil
          }
          // distribute the same source info to all annotations
          // todo: can we be more fine-grained? e.g., to pinpoint which post-condition is failing
          implicit def flattenAnnotationInfos(
            pair: (scala.Seq[AnnotationInfo], SourceInfo)) :
          Iterable[(AnnotationInfo, SourceInfo)] =
            pair._1.map(info => (info, pair._2))

          (f, (for (annot <- annots) yield {
            (AnnotationParser(annot), getSourceInfo(annot))
          }).toSeq.flatten)
      }.toMap

    // functions for which contracts should be generated
    // todo: generate contracts for ACSL annotated funs
    val contractFuns : scala.Seq[Afunc] =
      functionAnnotations.filter(_._2.exists(_._1 == ContractGen)).keys.toSeq

    val funsThatMightHaveACSLContracts : Map[Afunc, scala.Seq[(AnnotationInfo, SourceInfo)]] =
      functionAnnotations.filter(_._2.exists(_._1.isInstanceOf[MaybeACSLAnnotation]))

    for(fun <- contractFuns ++ funsThatMightHaveACSLContracts.keys) {
      val funDef = FuncDef(fun.function_def_)
      scope.LocalVars.pushFrame
      pushArguments(fun.function_def_)
      val functionParams = scope.LocalVars getVarsInTopFrame

      val oldVars = scope.allFormalVars map (v =>
        new CCVar(v.name + Literals.preExecSuffix, v.srcInfo, v.typ, v.storage))
      // the pre-condition: f_pre(preOldVars)
      val prePred = newPred(funDef.name + Literals.predPreSuffix, oldVars,
        Some(getSourceInfo(fun)))

      // the post-condition: f_post(oldVars, postGlobalVars, postResVar)
      // we first pass all current vars in context as old vars (oldVars)
      // then we pass all effected output vars (which are globals + resVar)
      val postGlobalVars = scope.GlobalVars.vars map (v =>
        new CCVar(v.name + Literals.postExecSuffix, v.srcInfo, v.typ, v.storage))
      val postResVar = getType(fun.function_def_) match {
        case CCVoid => None
        case _ => Some(new CCVar(funDef.name + Literals.resultExecSuffix,
          Some(funDef.sourceInfo), getType(fun.function_def_), AutoStorage)) // todo: clean this (and similar code) up a bit
      }
      val postVars = oldVars ++ postGlobalVars ++ postResVar
      functionPostOldArgs.put(funDef.name, oldVars)

      val prePredArgACSLNames = scope.allFormalVars map (_.name)
      val postPredACSLArgNames =
        scope.allFormalVars.map(v => "\\old(" + v.name + ")") ++
        scope.GlobalVars.vars.map(v => v.name) ++
        (if(postResVar nonEmpty) scala.Seq("\\result") else Nil)

      val postOldVarsMap: Map[String, CCVar] =
      (scope.allFormalVars.map(_ name) zip oldVars).toMap
      val postGlobalVarsMap: Map[String, CCVar] =
        (scope.GlobalVars.vars.map(_ name) zip postGlobalVars).toMap

      val postPred = newPred(funDef.name + Literals.predPostSuffix, postVars,
        Some(getSourceInfo(fun))) // todo: end line of fun?

      scope.LocalVars.popFrame

      class ReaderFunctionContext extends ACSLTranslator.FunctionContext {
        def getOldVar(ident: String): Option[CCVar] =
          postOldVarsMap get ident

        def getPostGlobalVar(ident: String): Option[CCVar] =
          postGlobalVarsMap get ident

        def getParams: scala.Seq[CCVar] = functionParams

        def getGlobals: scala.Seq[CCVar] =
          scope.GlobalVars.vars.diff(heapVars.values.toSeq).toSeq

        def getResultVar: Option[CCVar] = postResVar

        def isHeapEnabled: Boolean = modelHeap

        def getHeap: Heap =
          if (modelHeap) heap else throw NeedsHeapModelException

        private def getHeapModel: HeapModel =
          if (modelHeap) functionContexts(funDef.name).heapModel.get
          else throw NeedsHeapModelException

        // TODO: these need to be adapted for the new heap model interface
        def getHeapTerm: ITerm =
          if (modelHeap) getHeapModel.getACSLPostStateHeapTerm(this)
          else throw NeedsHeapModelException

        def getOldHeapTerm: ITerm =
          if (modelHeap) getHeapModel.getACSLPreStateHeapTerm(this)
          else throw NeedsHeapModelException

        def sortWrapper(s: Sort): Option[MonoSortedIFunction] =
          sortWrapperMap.get(s)

        def sortGetter(s: Sort): Option[MonoSortedIFunction] =
          sortGetterMap.get(s)

        def wrapperSort(wrapper: IFunction): Option[Sort] = wrapper match {
          case w: MonoSortedIFunction =>
            wrapperSortMap.get(w)
          case _ => None
        }

        def getterSort(getter: IFunction): Option[Sort] = getter match {
          case g: MonoSortedIFunction =>
            getterSortMap.get(g)
          case _ => None
        }

        def getTypOfPointer(t: CCType): CCType = t match {
          case p : CCHeapPointer => p.typ
          case t => t
        }

        def getCtor(s: Sort): Int = sortCtorIdMap(s)

        override val getStructMap: Map[IFunction, CCStruct] = {
          structDefs.values.map(struct => (struct.ctor, struct)).toMap
        }

        override val annotationBeginSourceInfo : SourceInfo = getSourceInfo(fun)

        override val annotationNumLines : Int = // todo: this is currently incorrect - to be fixed!
          functionAnnotations(fun).head._1 match {
            case inv : MaybeACSLAnnotation => inv.annot.count(_ == '\n')+1
            case _ => 1
          }
      }

      val funContext = new FunctionContext(prePred, postPred,
        new ReaderFunctionContext, prePredArgACSLNames, postPredACSLArgNames, heapModel)
      functionContexts += ((funDef.name, funContext))
    }

    val annotatedFuns : Map[Afunc, FunctionContract] =
      for ((fun, annots) <- funsThatMightHaveACSLContracts;
        (annot, srcInfo) <- annots if annot.isInstanceOf[MaybeACSLAnnotation]) yield {

        val name = getName(fun.function_def_)
        val funContext = functionContexts(name)
        val possibleACSLAnnotation = annot.asInstanceOf[MaybeACSLAnnotation]
        // todo: try / catch and print msg?
        val contract = ACSLTranslator.translateACSL(
          "/*@" + possibleACSLAnnotation.annot + "*/", funContext.acslContext)

        prePredsToReplace.add(funContext.prePred.pred)
        postPredsToReplace.add(funContext.postPred.pred)
        funToPreAtom.put(name, atom(funContext.prePred))
        funToPostAtom.put(name, atom(funContext.postPred))
        funsWithAnnot.add(name)
        val funContract = contract.asInstanceOf[FunctionContract]
        funToContract.put(name, funContract)

        (fun, funContract)
      }

    // ... and generate clauses for those functions
    for (f <- (contractFuns ++ annotatedFuns.keys).distinct) {
      import HornClauses._

      val funDef = FuncDef(f.function_def_)
      val name = funDef.name
      val typ = getType(f.function_def_)
      val funContext = functionContexts(name)
      val (prePred, postPred) = (funContext.prePred, funContext.postPred)
      setPrefix(name)

      scope.LocalVars.pushFrame
      val stm = pushArguments(f.function_def_)

      val prePredArgs = scope.allFormalVarTerms.toList

      for (v <- functionPostOldArgs(name)) scope.LocalVars addVar v

      val entryPred = newPred(Nil, Some(getSourceInfo(f)))

      val resVar = scope.getResVar(typ)
      val exitPred = newPred(resVar, Some(getLastSourceInfo(funDef.body)))

      output(addRichClause(
        entryPred(prePredArgs ++ prePredArgs) :- prePred(prePredArgs),
        Some(funDef.sourceInfo)))// todo: correct source info?

      val translator = FunctionTranslator(exitPred, name)
      val finalPred = typ match {
        case CCVoid =>
          translator.translateNoReturn(stm, entryPred)
          exitPred
        case _          =>
          translator.translateWithReturn(stm, entryPred)
      }

      val globalVarTerms : scala.Seq[ITerm] = scope.GlobalVars.formalVarTerms
      val postArgs : scala.Seq[ITerm] = (scope.allFormalVarTerms drop prePredArgs.size) ++
        globalVarTerms ++ resVar.map(v => IConstant(v.term)).toSeq

      output(addRichClause(
        postPred(postArgs) :-
          exitPred(scope.allFormalVarTerms ++ resVar.map(v => IConstant(v.term))),
        Some(funDef.sourceInfo) // todo: get last line number of function
      ))

      if (timeInvariants nonEmpty)
        throw new TranslationException(
          "Contracts cannot be used for functions with time invariants")
      if (clauses exists (_._2 != ParametricEncoder.NoSync))
        throw new TranslationException(
          "Contracts cannot be used for functions using communication channels")

      functionClauses.put(name, functionClauses.getOrElse(name, Nil) ++ clauses)
      functionAssertionClauses.put(name,
        functionAssertionClauses.getOrElse(name, Nil) ++ assertionClauses)

      clauses.clear
      assertionClauses.clear

      scope.LocalVars popFrame
    }

    // then translate the threads
    atomicMode = false

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_.asScala)
      decl match {
        case decl : Athread =>
          decl.thread_def_ match {
            case thread : SingleThread => {
              setPrefix(thread.cident_)
              val translator = FunctionTranslator.apply(thread.cident_)
              val finalPred = translator translateNoReturn(thread.compound_stm_)
              processes += ((clauses.toList, ParametricEncoder.Singleton))
              clauses.clear
            }
            case thread : ParaThread => {
              setPrefix(thread.cident_2)
              scope.LocalVars pushFrame
              val threadVar = new CCVar(thread.cident_1,
                Some(getSourceInfo(thread)), CCInt, AutoStorage)
              scope.LocalVars addVar threadVar
              val translator = FunctionTranslator.apply(thread.cident_2)
              val finalPred = translator translateNoReturn(thread.compound_stm_)
              processes += ((clauses.toList, ParametricEncoder.Infinite))
              clauses.clear
              scope.LocalVars popFrame
            }
          }

        case _ =>
          // nothing
      }

    if (functionClauses contains entryFunction) {
      hasACSLEntryFunction = true
      // do not encode entry function clauses if they are already generated
      processes +=
        ((functionClauses(entryFunction), ParametricEncoder.Singleton))
      assertionClauses ++= functionAssertionClauses(entryFunction)
      functionClauses remove entryFunction
      functionAssertionClauses remove entryFunction
    }
    else {
      // is there a global entry point in the program?
      (functionDefs get entryFunction) match {
        case Some(funDef) => {
          setPrefix(entryFunction)

          scope.LocalVars pushFrame

          val f = FuncDef(funDef)

          val returnType = {
            FuncDef(funDef).declSpecs match {
              case Some(declSpec) => getType(declSpec)
              case None => CCVoid
            }
          }

          val exitVar = scope.getResVar(returnType)
          val exitPred = newPred(exitVar, Some(getLastSourceInfo(f.body)))

          val stm = pushArguments(funDef)

          val translator = FunctionTranslator(exitPred, f.name)

          /**
           * There can be various ways out of a function. If a function has a
           * return type, the function can still end without reaching a
           * return statement - which is why there can be multiple `finalPreds`.
           */
          val finalPreds = scala.Seq(globalExitPred) ++ (
            if (returnType != CCVoid) {
              val exitWithoutReturnPred = translator.translateWithReturn(stm)
              scala.Seq(exitWithoutReturnPred, exitPred)
            }
            else scala.Seq(translator.translateNoReturn(stm)))

          /** The heap model might want to add some final assertions, for
           *  instance assertions related to memory safety. */
          if(modelHeap)
            heapModel.get.getExitAssertions(finalPreds).foreach(assertionClauses +=)

          processes += ((clauses.toList, ParametricEncoder.Singleton))
          clauses.clear

          scope.LocalVars popFrame
        }
        case None =>
          warn("entry function \"" + entryFunction + "\" not found")
      }
    }

    // remove assertions that are no longer connected to predicates
    // actually occurring in the system

    val allPreds =
      (for ((cls, _) <- processes.iterator;
            (c, _) <- cls.iterator;
            p <- c.predicates.iterator)
       yield p).toSet

    val remainingAssertions =
      assertionClauses filter { c => c.clause.bodyPredicates subsetOf allPreds }
    assertionClauses.clear
    assertionClauses ++= remainingAssertions
  }

  //////////////////////////////////////////////////////////////////////////////
  private def collectStructDefs(dec : Dec) : Unit = {
    dec match {
      case decl : Declarators => { // todo: check for multiple type specs
        val typ = decl.listdeclaration_specifier_.asScala
                      .find(_.isInstanceOf[Type]) match {
          case Some(t) => t.asInstanceOf[Type].type_specifier_
          case None => throw new
              TranslationException("Could not determine type for " + decl)
        }
        typ match {
          case structDec : Tstruct =>
            structDec.struct_or_union_spec_ match {
              case _: Unique =>
                val declarator = decl.listinit_declarator_.asScala.head match {
                  case initDecl: OnlyDecl     => initDecl.declarator_
                  case initDecl: HintDecl     => initDecl.declarator_
                  case initDecl: InitDecl     => initDecl.declarator_
                  case initDecl: HintInitDecl => initDecl.declarator_
                }
                collectStructInfo(structDec)
              case _ => collectStructInfo(structDec) // use X in "struct X"
            }
          case _ => // do nothing
        }
      }
      case nodecl : NoDeclarator => {
        val typ = nodecl.listdeclaration_specifier_.asScala.head match {
          case spec : Type => spec.type_specifier_
          case _ => throw new
              TranslationException("Storage and SpecProp not implemented yet")
        }
        typ match {
          case structSpec : Tstruct =>
            val structName = getStructName(structSpec)
            if (structSpec.struct_or_union_spec_.isInstanceOf[TagType])
              structInfos += StructInfo(structName, List())
            else collectStructInfo(structSpec)
          case enumDec : Tenum => buildEnumType(enumDec)
          case _ =>
        }
      }
      case preddecl : PredDeclarator => // nothing
      case interpPredDecl : InterpPredDeclarator => // nothing
    }
  }

  private def isUniqueStruct(listDec : ListDeclaration_specifier)
  : Boolean = listDec.asScala.headOption match {
    case Some(t : Type) =>
      t.type_specifier_ match {
        case s: Tstruct =>
          s.struct_or_union_spec_ match {
            case _ : Unique => true
            case _         => false
          }
        case _ => false
      }
    case _ => false
  }

  case object InitDeclaratorWrapper {
    def apply(initDecl : Init_declarator) : InitDeclaratorWrapper = {
      val srcInfo = getSourceInfo(initDecl)
      initDecl match {
        case initDecl : OnlyDecl => InitDeclaratorWrapper(
          initDecl.declarator_, None, Nil, srcInfo)
        case initDecl : HintDecl =>
          InitDeclaratorWrapper(
            initDecl.declarator_, None, initDecl.listannotation_.asScala.toSeq, srcInfo)
        case initDecl : InitDecl => InitDeclaratorWrapper(
          initDecl.declarator_, Some(initDecl.initializer_), Nil, srcInfo)
        case initDecl : HintInitDecl => InitDeclaratorWrapper(
          initDecl.declarator_, Some(initDecl.initializer_),
          initDecl.listannotation_.asScala.toSeq, srcInfo)
      }
    }
  }
  case class InitDeclaratorWrapper(declarator       : Declarator,
                                   maybeInitializer : Option[Initializer],
                                   hints            : scala.Seq[Annotation],
                                   sourceInfo       : SourceInfo)

  /**
   * @param dec               The declaration to collect from.
   * @param isGlobal          If this is a global declaration
   */
  private[concurrency]
  def collectVarDecls(dec      : Dec,
                      isGlobal : Boolean) : scala.Seq[CCDeclaration] = {
    dec match {
      case decl: Declarators => {
        // S D1, D2, D3, ...
        // in C, the type of a variable is the spec type that can be further
        //   modified in init declarators. Above S is the specType.
        // example: int x1, *x2, *x3[];
        // first one is an int, second one is an int*, last is an array of int*s
        val specType = getType(decl.listdeclaration_specifier_)
        val isStatic = decl.listdeclaration_specifier_.asScala.exists {
          case s : Storage =>
            s.storage_class_specifier_.isInstanceOf[LocalProgram]
          case _ => false
        }

        // each iteration is for one of the initDecls, above D1, D2, D3
        for (initDecl <- decl.listinit_declarator_.asScala.toSeq) yield {
          val initDeclWrapper = InitDeclaratorWrapper(initDecl)
          val name = getName(initDeclWrapper.declarator)
          val (typeWithPtrs, directDecl) = initDeclWrapper.declarator match {
            case decl: NoPointer =>
              (specType, decl.direct_declarator_)
            case decl: BeginPointer =>
              (getPtrType(decl.pointer_, specType), decl.direct_declarator_)
          }
          directDecl match {
            // function declaration
            case _: NewFuncDec /* | _ : OldFuncDef */ | _: OldFuncDec =>
              CCFunctionDeclaration(name, typeWithPtrs, directDecl,
                initDeclWrapper.sourceInfo) // todo: check that typeWithPtrs is correct here
            // array declaration
            case _: InitArray | _: Incomplete if !TriCeraParameters.parameters.value.useArraysForHeap =>
              val (arrayType, initArrayExpr) = {
                val (arrayLocation, initArrayExpr) = directDecl match {
                  case a: InitArray if isGlobal =>
                    (ArrayLocation.Global, Some(a.constant_expression_))
                  case a: InitArray if !isGlobal =>
                    (ArrayLocation.Stack, Some(a.constant_expression_))
                  case _ => (ArrayLocation.Heap, None)
                }
                (CCHeapArrayPointer(heap, typeWithPtrs, arrayLocation), initArrayExpr)
              }
              // todo: adjust needsHeap below if an array type does not require heap
              // for instance if we model arrays using the theory of arrays or unroll
              CCVarDeclaration(name, arrayType, initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = true, isStatic = isStatic,
                needsHeap = true, initArrayExpr = initArrayExpr,
                srcInfo = initDeclWrapper.sourceInfo)
            case _: InitArray | _: Incomplete if TriCeraParameters.parameters.value.useArraysForHeap =>
              val (arrayType, initArrayExpr) = {
                val (arrayLocation, initArrayExpr) = directDecl match {
                  case a: InitArray if isGlobal =>
                    (ArrayLocation.Global, Some(a.constant_expression_))
                  case a: InitArray if !isGlobal =>
                    (ArrayLocation.Stack, Some(a.constant_expression_))
                  case _ => (ArrayLocation.Heap, None)
                }
                (CCArray(typeWithPtrs, None, None, ExtArray(scala.Seq(CCInt.toSort), typeWithPtrs.toSort), arrayLocation), initArrayExpr)
              }
              // todo: adjust needsHeap below if an array type does not require heap
              // for instance if we model arrays using the theory of arrays or unroll
              CCVarDeclaration(name, arrayType, initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = true, isStatic = isStatic,
                needsHeap = false, initArrayExpr = initArrayExpr,
                srcInfo = initDeclWrapper.sourceInfo)
            case _ : MathArray =>
              CCVarDeclaration(name, CCArray(typeWithPtrs, None, None,
                ExtArray(scala.Seq(CCInt.toSort), typeWithPtrs.toSort),
                                             if(isGlobal) ArrayLocation.Global else ArrayLocation.Heap),
                initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = true, isStatic = isStatic,
                needsHeap = false, initArrayExpr = None,
                srcInfo = initDeclWrapper.sourceInfo)
            case _: Name =>
              CCVarDeclaration(name, typeWithPtrs, initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = false, isStatic = isStatic,
                needsHeap = false, initArrayExpr = None,
                srcInfo = initDeclWrapper.sourceInfo)
          }
        }
      }
      case noDecl: NoDeclarator =>
        scala.Seq(CCNoDeclaration)
      case predDecl: PredDeclarator =>
        scala.Seq(CCPredDeclaration(predDecl.listpred_hint_, getSourceInfo(predDecl)))
      case interpPredDecl: InterpPredDeclarator =>
        scala.Seq(CCInterpPredDeclaration(interpPredDecl.pred_interp_))
    }
  }

  /**
   * This is used for collecting argument names and types of interpreted
   * predicate expressions.
   */
  private def collectArgTypesAndNames(decList : ListParameter_declaration,
                                      declName : String = "") :
    scala.Seq[(CCType, String)] = {
    for (ind <- decList.asScala.indices) yield {
      decList.asScala(ind) match {
        case t : OnlyType => {
          if (t.listdeclaration_specifier_.asScala.exists(
            spec => !spec.isInstanceOf[Type]))
            throw new TranslationException(
              "Only type specifiers are allowed inside predicate declarations.")
          val argType = getType(
            t.listdeclaration_specifier_.asScala.map(_.asInstanceOf[Type]
                                              .type_specifier_).iterator)
          val argName = declName + "_" + ind
          (argType, argName)
        }
        case argDec : TypeAndParam => {
          val name = getName(argDec.declarator_)
          val typ  = getType(argDec.listdeclaration_specifier_)
          val actualType = argDec.declarator_ match {
            case p : BeginPointer => createHeapPointer(p, typ)
            case np : NoPointer   => np.direct_declarator_ match {
              case _ : Incomplete =>
                //CCHeapArrayPointer(heap, typ, HeapArray)
                throw new TranslationException(
                  "Arrays inside predicate declarations are not supported.")
              case _ => typ
            }
            case _ => typ
          }
          (actualType, name)
        }
        case argDec : TypeHintAndParam => {
          val name = getName(argDec.declarator_)
          val typ  = getType(argDec.listdeclaration_specifier_)
          val actualType = argDec.declarator_ match {
            case p : BeginPointer => createHeapPointer(p, typ)
            case _ => typ
          }
          processHints(argDec.listannotation_) // todo: does this work??
          (actualType, name)
        }
        case argDec : Abstract => {
          val typ  = getType(argDec.listdeclaration_specifier_)
          val actualType = argDec.abstract_declarator_ match {
            case p : PointerStart => createHeapPointer(p, typ)
            case _ => throw new TranslationException(
              s"Unsupported declaration inside predicate declaration: ${printer.print(argDec)}")
          }
          val argName = declName + "_" + ind
          (actualType, argName)
        }
      }
    }
  }

  /**
   * Collects variable declarations and stores them in [[scope.GlobalVars]] and
   * [[scope.LocalVars]] (depending on the value of `isGlobal`. It also stores
   * their initial values in the passed `values` [[Symex]].
   * @param dec               The declaration to collect from.
   * @param isGlobal          If this is a global declaration
   * @param values            This [[Symex]] will be used to fill in the
   *                          extracted values.
   * @param enclosingFuncName Current function (if not global)
   * @param collectOnlyLocalStatic If set, signals this is collecting static
   *                               local variables.
   *                          **/
  private def collectVarDecls(dec                    : Dec,
                              isGlobal               : Boolean,
                              values                 : Symex,
                              enclosingFuncName      : String = "",
                              collectOnlyLocalStatic : Boolean) : Unit = {
    if(collectOnlyLocalStatic)
      assert(enclosingFuncName nonEmpty)
    val decls = collectVarDecls(dec, isGlobal || collectOnlyLocalStatic)
    for (decl <- decls) decl match {
      case funDec : CCFunctionDeclaration =>
        functionDecls.put(funDec.name, (funDec.directDecl, funDec.typ))
      case varDec : CCVarDeclaration
        if !isGlobal && (
             varDec.isStatic && !collectOnlyLocalStatic ||
             !varDec.isStatic && collectOnlyLocalStatic) =>
      /**
       * Do nothing when collecting non-global variables and
       * - collecting static variables & this is a non-static variable
       * - collecting non-static variables & this is a static variable (handled before)
       */
      case varDec : CCVarDeclaration
        if collectOnlyLocalStatic && varDec.isStatic || !collectOnlyLocalStatic =>
        /**
         * Collect the variables when
         * - collecting static variables and this is a static one,
         * - collecting non-static variables
         */
        if(!modelHeap && varDec.needsHeap)
          throw NeedsHeapModelException

        val storage = {
          if (isGlobal) GlobalStorage // ignore static in globals
          else if (varDec.isStatic) StaticStorage(enclosingFuncName)
          else AutoStorage
        }

        val lhsVar = new CCVar(varDec.name, Some(varDec.srcInfo), varDec.typ,
                               storage)
        val srcInfo = lhsVar.srcInfo

        val (actualLhsVar, initValue, initGuard) =
          varDec.maybeInitializer match {
            case Some(init : InitExpr) if init.exp_.isInstanceOf[Enondet] => 
              lhsVar.typ match {
                case typ : CCHeapArrayPointer =>
                  val resultExpr =
                    values.handleUninitializedArrayDecl(
                      typ, varDec.initArrayExpr, isGlobal || collectOnlyLocalStatic, true)
                  (lhsVar, resultExpr, IExpression.i(true))
                case _ =>
                  (lhsVar, CCTerm.fromTerm(lhsVar.term, varDec.typ, srcInfo),
                   lhsVar rangePred)
              }
            case Some(init : InitExpr) if !init.exp_.isInstanceOf[Enondet] =>
                // discard useless type conversions
                val actualInitExp = init.exp_ match {
                  case typeConv : Etypeconv
                    if getType(typeConv.type_name_) == lhsVar.typ =>
                    typeConv.exp_
                  case _ => init.exp_
                }

                val evalContext =
                  if (varDec.typ.isInstanceOf[CCHeapArrayPointer])
                    values.EvalContext().withLhsIsArrayPointer(true)
                  else values.EvalContext()
                val res = values.eval(actualInitExp)(
                  values.EvalSettings(), evalContext)
                val (actualLhsVar, actualRes) = lhsVar.typ match {
                  case _ : CCHeapPointer if res.typ.isInstanceOf[CCArithType] =>
                    if(res.toTerm.asInstanceOf[IIntLit].value.intValue == 0)
                      (lhsVar, CCTerm.fromTerm(heap.nullAddr(), varDec.typ, srcInfo))
                    else throw new TranslationException("Pointer arithmetic is not " +
                      "allowed, and the only possible initialization value for " +
                      "pointers is 0 (NULL)")
                  case _ : CCHeapPointer if res.typ.isInstanceOf[CCHeapArrayPointer] =>
                    // lhs is actually a heap array pointer
                    (new CCVar(lhsVar.name, lhsVar.srcInfo, res.typ,
                               lhsVar.storage), res)
                  case _ : CCHeapPointer if res.typ.isInstanceOf[CCStackPointer] =>
                    // lhs is actually a stack pointer
                    (new CCVar(lhsVar.name, lhsVar.srcInfo, res.typ,
                               lhsVar.storage), res)
                  case _ => (lhsVar, res)
                }
                (actualLhsVar, actualRes, IExpression.i(true))
            case Some(_ : InitListOne) | Some(_: InitListTwo) => {
              val initStack =
                getInitsStack(varDec.maybeInitializer.get, values)
              varDec.typ match {
                case structType : CCStruct =>
                  (lhsVar, CCTerm.fromTerm(structType.getInitialized(initStack), varDec.typ, srcInfo),
                    lhsVar rangePred)
                case arrayPtr : CCHeapArrayPointer =>
                  val addressRangeValue = varDec.initArrayExpr match {
                    case Some(expr) =>
                      val arraySizeTerm =
                        values.eval(expr.asInstanceOf[Especial].exp_)(
                          values.EvalSettings(), values.EvalContext())
                      values.handleArrayInitialization(
                        arrayPtr, arraySizeTerm, initStack,
                        values.getStaticLocationId(varDec.srcInfo)).toTerm
                    case None =>
                      throw new TranslationException("Cannot initialize" +
                        "arrays with unknown size")
                  }
                  // initialise using the first address of the range
                  (lhsVar, CCTerm.fromTerm(
                    addressRangeValue, varDec.typ, srcInfo), IExpression.i(true))
                case s =>
                  println(s)
                  throw new TranslationException("Union list " +
                    "initialization is not yet supported.")
              }
            }
            case Some(_) => throw new UnsupportedCFragmentException(
              getLineStringShort(srcInfo) + " Unsupported initializer expression.")
            case None =>
              varDec.typ match {
                case typ : CCHeapArrayPointer =>
                  val resultExpr =
                    values.handleUninitializedArrayDecl(
                      typ, varDec.initArrayExpr, isGlobal || collectOnlyLocalStatic, TriCeraParameters.parameters.value.forceNondetInit)
                  (lhsVar, resultExpr, IExpression.i(true))
                case _ if (isGlobal || collectOnlyLocalStatic) && !TriCeraParameters.parameters.value.forceNondetInit =>
                  (lhsVar, CCTerm.fromTerm(varDec.typ.getZeroInit, varDec.typ, srcInfo),
                    lhsVar rangePred)
                case _ =>
                  (lhsVar, CCTerm.fromTerm(lhsVar.term, varDec.typ, srcInfo),
                    lhsVar rangePred)
              }
          }

        // do not use actualType below, take from lhsVar

        if (isGlobal || collectOnlyLocalStatic) {
          scope.GlobalVars addVar actualLhsVar
          scope.variableHints += List()
        } else {
          scope.LocalVars addVar actualLhsVar
        }

        actualLhsVar.typ match {
          case CCClock =>
            values addValue translateClockValue(initValue)
          case CCDuration =>
            values addValue translateDurationValue(initValue)
          case _ =>
            values addValue (actualLhsVar.typ cast initValue)
        }

        values addGuard (
          if(varDec.typ == actualLhsVar.typ) initGuard
          else actualLhsVar rangePred
        )

        // parse possible model checking hints
        processHints(varDec.hints)

      case predDec : CCPredDeclaration =>
        for (hint <- predDec.predHints.asScala) {
          hint match {
            case predHint : PredicateHint =>
              // todo: refactor this using other code collecting parameter information
              val decList = predHint.parameter_type_.asInstanceOf[AllSpec]
                .listparameter_declaration_
              val argTypesAndNames : scala.Seq[(CCType, String)] =
                collectArgTypesAndNames(decList, predHint.cident_)
              val srcInfo = Some(getSourceInfo(predHint))
              val argCCVars = // needed for adding to predCCPredMap, used in printing
                argTypesAndNames.map{case (argType, argName) =>
                  new CCVar(argName, srcInfo, argType, AutoStorage)}
              val hintPred = newPred(predHint.cident_, argCCVars, srcInfo)
              uninterpPredDecls += ((predHint.cident_, hintPred))
          }
        }
      case interpPredDec : CCInterpPredDeclaration =>
        interpPredDec.predDecl match {
          case predExp : PredicateExp =>
            val decList = predExp.parameter_type_.asInstanceOf[AllSpec].
                                 listparameter_declaration_
            val argTypesAndNames : scala.Seq[(CCType, String)] =
              collectArgTypesAndNames(decList, predExp.cident_)

            val ccVars = argTypesAndNames.map{
              case (typ, name) =>
                new CCVar(name, Some(getSourceInfo(predExp)), typ, AutoStorage)
            }
            values.saveState
            ccVars.foreach(scope.LocalVars addVar)
            for ((ccVar, ind) <- ccVars.zipWithIndex) {
              values.addValue(CCTerm.fromTerm(IExpression.v(ind), ccVar.typ, ccVar.srcInfo))
            }
            val predFormula : CCTerm =
              values.eval(predExp.exp_)(values.EvalSettings(
                noClausesForExprs = true), values.EvalContext()) match {
              case f : CCTerm if f.originalFormula.nonEmpty => f
              case _ => throw new TranslationException("Only Boolean " +
                "expressions are supported inside interpreted predicate " +
                "declarations.")
            }
            values.restoreState
            interpPredDefs += predExp.cident_ -> predFormula
        }
      case CCNoDeclaration => // todo: nothing?
    }
  }

  private def processHints(hintAnnotations : ListAnnotation) : Unit =
    processHints(hintAnnotations.asScala.toSeq)
  private def processHints(hintAnnotations : scala.Seq[Annotation]) : Unit = {
    val hints : scala.Seq[AbsHintClause] = (for (hint <- hintAnnotations) yield {
      AnnotationParser(hint)
    }).flatten.filter(_.isInstanceOf[AbsHintClause]).
      map(_.asInstanceOf[AbsHintClause])
    if (hints.nonEmpty) {
      val hintSymex = Symex(symexContext, scope, null, heapModel)
      hintSymex.saveState

            val subst =
              (for ((v, n) <-
                      (scope.GlobalVars.iterator ++ scope.LocalVars.iterator).zipWithIndex)
               yield (v.term.asInstanceOf[ConstantTerm] -> IExpression.v(n))).toMap

      import AnnotationParser._
      val hintEls =
        for (hint <- hints;
             cost = hint.cost.getOrElse("1").toInt;
             e <- hint.exp_args match {
               case Some(args) => inAtomicMode(hintSymex evalList args)
               case None => Nil
             })
              yield hint.hint match {
                case Predicates => {
                  usingInitialPredicates = true
                  VerifHintInitPred(ConstantSubstVisitor(e.toFormula, subst))
                }
                case PredicatesTpl =>
                  VerifHintTplPred(ConstantSubstVisitor(e.toFormula, subst),
                                   cost)
                case TermsTpl =>
                  VerifHintTplEqTerm(ConstantSubstVisitor(e.toTerm, subst),
                                     cost)
                case _ =>
                  throw new TranslationException("cannot handle hint " +
                                                 hint.hint)
              }

            if (!hintSymex.atomValuesUnchanged)
              throw new TranslationException(
                "Hints are not side effect-free: " +
                hints.mkString(""))

            scope.variableHints(scope.variableHints.size - 1) = hintEls
          }
    }

  private def getType(specs : ListDeclaration_specifier) : CCType =
    getType(specs.asScala.toSeq)
  private def getType(specs : scala.Seq[Declaration_specifier]) : CCType =
    getType(for (specifier <- specs.iterator;
                 if (specifier.isInstanceOf[Type]))
            yield specifier.asInstanceOf[Type].type_specifier_)

  private def getPtrType (ptr : Pointer, _typ : CCType) : CCType = {
    ptr match {
      case _   : Point | _ : PointQual => CCHeapPointer(heap, _typ) // todo; support pointer qualifiers?
      case ptr : PointPoint =>
        getPtrType(ptr.pointer_, CCHeapPointer(heap, _typ))
      case _ => throw new TranslationException(
        "Advanced pointer declarations are not yet supported (line " +
          getSourceInfo(ptr).line + ")"
      )
    }
  }

  private def getType(name : Type_name) : CCType = name match {
    case name : PlainType =>
      getType(for (qual <- name.listspec_qual_.asScala.iterator;
                   if (qual.isInstanceOf[TypeSpec]))
              yield qual.asInstanceOf[TypeSpec].type_specifier_)
    case name : ExtendedType =>
      val typ = getType(for (qual <- name.listspec_qual_.asScala.iterator;
                   if (qual.isInstanceOf[TypeSpec]))
        yield qual.asInstanceOf[TypeSpec].type_specifier_)
      name.abstract_declarator_ match {
        case ptr: PointerStart => getPtrType(ptr.pointer_, typ)
        case _ => throw new TranslationException(
          "Advanced declarators are not yet supported: " + name
        )
      }
  }

  private def getType(exp : Ebytestype) : CCType = getType(exp.type_name_)

  // get type of struct field
  private def getType(fields : Struct_dec) : CCType = {
    val specs =
      (for (qual <- fields.asInstanceOf[Structen].listspec_qual_.asScala.iterator;
           if (qual.isInstanceOf[TypeSpec]))
        yield qual.asInstanceOf[TypeSpec].type_specifier_).toList
    specs.find(s => s.isInstanceOf[Tenum]) match {
      case Some(enum) => buildEnumType(enum.asInstanceOf[Tenum])
      case None =>
        val (maybeDecl, maybeConstExpr) =
          fields.asInstanceOf[Structen].liststruct_declarator_.asScala.head match {
            case f : Decl =>
              (Some(f.declarator_), None)
            case f : Field =>
              (None, f.constant_expression_)
            case f : DecField =>
              (Some(f.declarator_), Some(f.constant_expression_))
          }

        val typ = getType(specs.iterator)
        // todo: unify this with code from collectVarDecl
        val actualTyp = if (maybeDecl isEmpty) {
          typ
        } else {
          val (directDecl, isPointer, sourceInfo) = maybeDecl.get match {
            case decl: NoPointer => (decl.direct_declarator_, false,
              Some(getSourceInfo(decl)))
            case decl: BeginPointer => (decl.direct_declarator_, true,
              Some(getSourceInfo(decl)))
          }
          directDecl match {
            case _: NewFuncDec /* | _ : OldFuncDef */ | _: OldFuncDec =>
              throw new TranslationException("Functions as struct fields" +
                " are not supported.")
            case _: Incomplete if !TriCeraParameters.parameters.value.useArraysForHeap =>
              if (!modelHeap) throw NeedsHeapModelException
              CCHeapArrayPointer(heap, typ, ArrayLocation.Heap)
            case _: Incomplete if TriCeraParameters.parameters.value.useArraysForHeap =>
              CCArray(typ, None, None,
                ExtArray(scala.Seq(CCInt.toSort), typ.toSort), ArrayLocation.Heap) // todo: only int indexed arrays
            case initArray: InitArray =>
              val arraySizeSymex = Symex(symexContext, scope, null, heapModel)
              val evalSettings = arraySizeSymex.EvalSettings()
              val evalContext = arraySizeSymex.EvalContext()
              val arraySizeExp = arraySizeSymex.eval(
                initArray.constant_expression_.asInstanceOf[Especial].exp_)(
                evalSettings, evalContext
              )
              val arraySize = arraySizeExp match {
                case CCTerm(IIntLit(IdealInt(n)), typ, srcInfo, _)
                  if typ.isInstanceOf[CCArithType] => n
                case _ => throw new TranslationException("Array with non-integer" +
                  "size specified inside struct definition!")
              }
              CCArray(typ, Some(arraySizeExp), Some(arraySize),
                ExtArray(scala.Seq(arraySizeExp.typ.toSort), typ.toSort),
                      ArrayLocation.Heap)
            case _ => typ
          }
        }
        actualTyp
    }
  }

  private var anonCount = 0
  private def getAnonName(prefix : String): String = {
    anonCount += 1
    prefix + (anonCount - 1)
  }

  private def getAnonStructName: String =
    getAnonName(Literals.anonStructName)

  private def getAnonEnumName: String =
    getAnonName(Literals.anonEnumName)

  private def getStructName(spec: Tstruct) : String =
    spec.struct_or_union_spec_ match {
      case u : Unique => uniqueStructs.get(u) match {
        case Some(name) => name
        case None => throw new TranslationException("Unique struct was not" +
          " found!")
      }
      case tagged: Tag => tagged.cident_
      case tagged: TagType => tagged.cident_
    }

  private def collectStructInfo(spec: Tstruct) : Unit = {
    spec.struct_or_union_spec_ match {
      case _ : Unique => collectStructInfo(spec, getAnonStructName)
      case tagged : Tag => collectStructInfo(spec, tagged.cident_)
      case _ => // todo: do nothing for TagType
    }
  }

  private def collectStructInfo (spec: Tstruct,
                                 structName: String): Unit = {
    if (structInfos contains structName) //todo:what about shadowing?
      throw new TranslationException(
        "struct " + structName + " is already defined")

    val fields = spec.struct_or_union_spec_ match {
      case dec: Tag => dec.liststruct_dec_.asScala.toSeq
      case dec: Unique =>
        uniqueStructs += ((dec, structName))
        dec.liststruct_dec_.asScala.toSeq
      case _ => throw new TranslationException("struct can only be built" +
        "with Unique or Tag types!")
    }

    val fieldList : scala.IndexedSeq[FieldInfo] = (for (field <- fields) yield {

      // ignoring all qual specs such as volatile, const etc.
      val specs : List[Type_specifier] =
        (for (f <- field.asInstanceOf[Structen].listspec_qual_.asScala.toSeq
             if f.isInstanceOf[TypeSpec])
          yield f.asInstanceOf[TypeSpec].type_specifier_).toList

      // if specs has a struct or union field we cannot simply get the type,
      // as the field itself might be defining a struct or union
      val fieldType : Either[Integer, CCType] =
      specs.find(s => s.isInstanceOf[Tstruct]) match {
        case Some(ts) =>
          val t = ts.asInstanceOf[Tstruct]
          val typeName = t.struct_or_union_spec_ match {
            case _ : Unique =>
              val name = getAnonStructName
              collectStructInfo(t, name) // need to collect the struct info now
              //uniqueStructs += ((t, name))
              name
            case _ => getStructName(t)
          }
          structInfos.indexWhere(s => s.name == typeName) match {
            case -1 =>
              structInfos += StructInfo(typeName, List())
              Left(structInfos.size - 1)
            case i => Left(i)
          }
        // todo: get pointer depth
        /*case t : Tstruct if t.struct_or_union_spec_.isInstanceOf[TagType] &&
          (getStructName(t) == structName || structIsDeclared(getStructName(t))) &&
          field.asInstanceOf[Structen].liststruct_declarator_(0).asInstanceOf[Decl].declarator_.isInstanceOf[BeginPointer] =>
          CCDeclarationOnlyPointer(getStructName(t))
        //todo: some error handling here?
        case t : Tstruct if structInfos contains getStructName(t) =>
          getType(field)*/
        case _ => Right(getType(field))
      }
      val declarators = field.asInstanceOf[Structen].liststruct_declarator_.asScala.toSeq

      for (decl <- declarators if !decl.isInstanceOf[Field]) yield {
        val declarator = decl match {
          case d : Decl => d.declarator_
          case d : DecField => d.declarator_ // ignore bit field, only collect decl
        }

        val fieldName = getName(declarator)
        val ptrDepth = declarator match {
          case _ : BeginPointer => 1 //todo:heap find out actual depth
          case _ => 0
        }
        FieldInfo(fieldName, fieldType, ptrDepth) // todo: deal with pointer fields
      }
    }).toList.flatten.toIndexedSeq

    /*val ADTFieldList : List[(String, ap.theories.ADT.OtherSort)] =
      for((fieldName, fieldType) <- fieldList)
        yield (fieldName, ADT.OtherSort(fieldType.toSort))*/

    structInfos.indexWhere(s => s.name == structName) match {
      case -1 => structInfos += StructInfo(structName, fieldList)
      case i  =>
        if (structInfos(i).fieldInfos.nonEmpty) throw new TranslationException(
          "Struct name " + structName + " is used in more than one location, " +
            "this is currently not supported. As a workaround, please make " +
            "sure that all structs have unique names (even shadowed ones).")
        structInfos(i) = StructInfo(structName, fieldList)
    }
  }
  private def getInitsStack(init: Initializer, s: Symex): Stack[ITerm] = {
    val initStack = new Stack[ITerm]
    def fillInit(init: Initializer) {
      init match {
        case init: InitExpr =>
          initStack.push(s.eval(init.exp_)(
            s.EvalSettings(), s.EvalContext()).toTerm)
        case init: InitListOne => fillInits(init.initializers_)
        case init: InitListTwo => fillInits(init.initializers_)
      }
    }
    def fillInits(inits: Initializers) {
      inits match {
        case init: AnInit => fillInit(init.initializer_)
        case init: MoreInit => {
          fillInit(init.initializer_)
          fillInits(init.initializers_)
        }
      }
    }
    fillInit(init)
    initStack
  }

  private def getEnumType(spec: Tenum) : CCType =
    spec.enum_specifier_ match {
      case dec : EnumDec =>
        buildEnumType(dec.listenumerator_.asScala.toSeq, getAnonEnumName)
      case named : EnumName =>
        buildEnumType(named.listenumerator_.asScala.toSeq, named.cident_)
      case vared : EnumVar =>
        (enumDefs get vared.cident_) match {
          case Some(t) => t
          case None =>
            throw new TranslationException(
              "enum " + vared.cident_ + " is not defined")
        }
    }

    private def buildEnumType(spec: Tenum) : CCType = {
    spec.enum_specifier_ match {
      case dec : EnumDec =>
        buildEnumType(dec.listenumerator_.asScala.toSeq, getAnonEnumName)
      case named : EnumName =>
        buildEnumType(named.listenumerator_.asScala.toSeq, named.cident_)
      case _ => CCInt
    }
  }

  private def buildEnumType (specs: scala.Seq[Enumerator],
                             enumName: String) : CCType = {
    if (enumDefs contains enumName)
      throw new TranslationException(
        "enum " + enumName + " is already defined")

    def addEnumerator(name : String, t : CCTerm) = {
      if (enumeratorDefs contains name)
        throw new TranslationException(
          "enumerator " + name + " already defined")
      enumeratorDefs.put(name, t)
    }
    {
      // map the enumerators to integers directly
      var nextInd = IdealInt.ZERO
      var enumerators = new MHashMap[String, IdealInt]
      val symex = Symex(symexContext, scope, null, heapModel) // a temporary Symex to collect enum declarations
      // to deal with fields referring to same-enum fields, e.g. enum{a, b = a+1}
      scope.LocalVars pushFrame // we also need to add them as vars

      for (s <- specs) s match {
        case s : Plain => {
          val ind = nextInd
          nextInd = nextInd + 1
          val v = new CCVar(s.cident_, Some(getSourceInfo(s)), CCInt, AutoStorage)
          scope.LocalVars addVar v
          symex.addValue(CCTerm.fromTerm(IIntLit(ind), CCInt, v.srcInfo))
          enumerators += ((s.cident_, ind))
        }
        case s : EnumInit => {
          val ind = translateConstantExpr(s.constant_expression_, symex).toTerm match {
            case IIntLit(v) => v
            case ITimes(IdealInt(-1), IIntLit(v)) => -v
            case IPlus(IIntLit(v1), IIntLit(v2)) => v1 + v2
            case _ =>
              throw new TranslationException("cannot handle enumerator " +
                                             (printer print s))
          }
          nextInd = ind + 1
          val v = new CCVar(s.cident_,
            Some(getSourceInfo(s)), CCInt, AutoStorage)
          scope.LocalVars addVar v
          symex.addValue(CCTerm.fromTerm(IIntLit(ind), CCInt, v.srcInfo))
          enumerators += ((s.cident_, ind))
        }
      }

      scope.LocalVars popFrame

      val newEnum = CCIntEnum(enumName, enumerators.toSeq)
      enumDefs.put(enumName, newEnum)

      for ((n, v) <- enumerators)
        addEnumerator(n, CCTerm.fromTerm(v, newEnum, None)) // todo: srcInfo?
      newEnum
    }
  }

  /*private def updateArraySize (arrayTyp : CCArray, decl : OnlyDecl) = {
    if (arraySizes contains arrayTyp)
      throw new TranslationException(
        "size of " + arrayTyp + " is already defined")

    val symex = Symex(symexContext, scope, null) // a temporary Symex to collect the array size

    /*val arraySize = decl match {
      case initArray : InitArray => // todo: maybe this can be calculated beforehand, so we actually have an integer constant here?
        Some(symex.eval(initArray.constant_expression_.asInstanceOf[Especial].exp_)) // todo: n-d arrays?
      case _ : Incomplete => None // no size information
    }*/
    arraySizes += ((arrayTyp, arraySize))
  }*/

  private def getType(typespec : Type_specifier) : CCType = {
    getType(scala.Seq(typespec).iterator)
  }

  private def getType(specs : Iterator[Type_specifier]) : CCType = {
    // by default assume that the type is int
    var typ : CCType = CCInt

    for (specifier <- specs)
      specifier match {
            case _ : Tvoid =>
              typ = CCVoid
            case _ : Tint =>
              // ignore
            case _ : Tchar =>
              // ignore
            case _ : Tsigned =>
              typ = CCInt
            case _ : Tunsigned =>
              typ = CCUInt
            case _ : Tlong if typ == CCInt =>
              typ = CCLong
            case _ : Tlong if typ == CCUInt =>
              typ = CCULong
            case _ : Tlong if typ == CCLong =>
              typ = CCLongLong
            case _ : Tlong if typ == CCULong =>
              typ = CCULongLong
            case structOrUnion : Tstruct =>
              val structName = getStructName(structOrUnion)
              typ = structDefs get structName match {
                case None => throw new TranslationException(
                  "struct " + structName + " not found!")
                case Some(structType) => structType
              }
            case enum : Tenum =>
              typ = getEnumType(enum)
            case _ : Tclock => {
              if (!useTime)
                throw NeedsTimeException
              typ = CCClock
            }
            case _ : Tduration => {
              if (!useTime)
                throw NeedsTimeException
              typ = CCDuration
            }
            case _ : THeapObject => {
              if (!modelHeap)
                throw NeedsHeapModelException
              typ = CCHeapObject(heap)
            }
            case x => {
              warn("type " + (printer print x) +
                   " not supported, assuming int")
              typ = CCInt
            }
          }
    typ
  }

  private def getType(functionDef : Function_def) : CCType = {
    val f = FuncDef(functionDef)
    val typ = f.declSpecs match {
      case Some(listDeclSpecs) =>
        getType(listDeclSpecs)
      case None => CCInt
    }
    if(f.decl.isInstanceOf[BeginPointer]) CCHeapPointer(heap, typ) // SSSOWO Still relevant: todo: can be stack pointer too, this needs to be fixed
    else typ
  }

  private def translateClockValue(expr : CCTerm) : CCTerm = {
    import IExpression._
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm.fromTerm(GT.term + GTU.term*(-v), CCClock, expr.srcInfo)
      case t if (expr.typ == CCClock) =>
        CCTerm.fromTerm(t, CCClock, expr.srcInfo)
      case t if (expr.typ == CCDuration) =>
        CCTerm.fromTerm(GT.term - t, CCClock, expr.srcInfo)
      case t =>
        throw new TranslationException(
          "clocks can only be set to or compared with integers")
    }
  }

  private def translateDurationValue(expr : CCTerm) : CCTerm = {
    import IExpression._
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case _ if (expr.typ == CCDuration) =>
        expr
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm.fromTerm(GTU.term*v, CCDuration, expr.srcInfo)
      case t =>
        throw new TranslationException(
          "duration variable cannot be set or compared to " + t)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateConstantExpr(expr : Constant_expression,
                                    symex : Symex =
                                    Symex(symexContext, scope, null, heapModel))
  : CCTerm = {
    symex.saveState
    val res = symex.eval(expr.asInstanceOf[Especial].exp_)(
      symex.EvalSettings(), symex.EvalContext())
    if (!symex.atomValuesUnchanged)
      throw new TranslationException(
        "constant expression is not side-effect free")
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  private def atom(ccPred : CCPredicate, args : scala.Seq[ITerm]) : IAtom = {
    if (ccPred.arity != args.size) {
      throw new TranslationException(getLineString(ccPred.srcInfo) +
        s"$ccPred expects ${ccPred.arity} argument(s)" +
        s", but got ${args.size}: " + args.mkString(", "))
    }
    IAtom(ccPred.pred, args)
  }
  private def atom(ccPred : CCPredicate) : IAtom =
    atom(ccPred, ccPred.argVars.map(_.term))

  //////////////////////////////////////////////////////////////////////////////

  private def inlineFunction(functionDef : Function_def,
                             entry : CCPredicate,
                             exit : CCPredicate,
                             args : List[CCType],
                             isNoReturn : Boolean,
                             functionName : String) : Unit = {
    scope.LocalVars pushFrame
    val stm = pushArguments(functionDef, args)

    // this might be an inlined function in an expression where we need to
    // carry along other terms that were generated in the expression, so this
    // assertion is not necessarily true:
    // assert(entry.arity == scope.allFormalVars.size)

    val translator = FunctionTranslator(exit, functionName)
    val finalPred =
      if (isNoReturn) {
        translator.translateNoReturn(stm, entry)
        exit
      } else
        translator.translateWithReturn(stm, entry)
    scope.LocalVars popFrame
  }

  private def createHeapPointer(decl : BeginPointer, typ : CCType) :
  CCHeapPointer = createHeapPointerHelper(decl.pointer_, typ)

  private def createHeapPointer(decl : PointerStart, typ : CCType) :
  CCHeapPointer = createHeapPointerHelper(decl.pointer_, typ)

  private def createHeapPointerHelper(decl : Pointer, typ : CCType) :
  CCHeapPointer = decl match {
      case pp : PointPoint =>
        CCHeapPointer(heap, createHeapPointerHelper(pp.pointer_, typ))
      case p : Point =>
        CCHeapPointer(heap, typ)
      case _ => throw new TranslationException("Type qualified pointers are " +
        "currently not supported: " + decl)
    }

  private def getFunctionArgNames(functionDef : Function_def) : scala.Seq[String] = {
    val f = FuncDef(functionDef)
    val decl = f.decl match {
      case noPtr : NoPointer => noPtr.direct_declarator_
      case ptr   : BeginPointer => ptr.direct_declarator_
    }
    decl match {
      case dec : NewFuncDec =>
        val decList = dec.parameter_type_.asInstanceOf[AllSpec]
          .listparameter_declaration_.asScala
        val argNames = new ArrayBuffer[String]
        for (ind <- decList.indices)
          decList(ind) match {
            case _ : OnlyType =>
            // a void argument implies that there are no arguments
            case argDec : TypeAndParam =>
              argNames += getName(argDec.declarator_)
            case argDec : TypeHintAndParam =>
              argNames += getName(argDec.declarator_)
          }
        argNames.toSeq
      case dec : OldFuncDec =>
      // arguments are not specified ...
        Nil
    }
  }

  // todo: refactor this to separate parsing and pushing
  private def pushArguments(functionDef : Function_def,
                            pointerArgs : List[CCType] = Nil) : Compound_stm = {
    val f = FuncDef(functionDef)
    val decl = f.decl match {
      case noPtr : NoPointer => noPtr.direct_declarator_
      case ptr   : BeginPointer => ptr.direct_declarator_
    }
    decl match {
      case dec : NewFuncDec =>
        val decList = dec.parameter_type_.asInstanceOf[AllSpec]
          .listparameter_declaration_.asScala
        for (ind <- decList.indices)
          decList(ind) match {
            case _ : OnlyType =>
              // ignore, a void argument implies that there are no arguments
            case argDec : TypeAndParam =>
              val name = getName(argDec.declarator_)
              val typ = getType(argDec.listdeclaration_specifier_)
              val actualType = argDec.declarator_ match {
                case _: BeginPointer if pointerArgs.nonEmpty => pointerArgs(ind)
                case p : BeginPointer =>
                  createHeapPointer(p, typ)
                case np : NoPointer =>
                  np.direct_declarator_ match {
                    case _ : Incomplete
                      if !TriCeraParameters.parameters.value.useArraysForHeap =>
                      CCHeapArrayPointer(heap, typ, ArrayLocation.Heap)
                    case _ : Incomplete
                      if TriCeraParameters.parameters.value.useArraysForHeap =>
                      CCArray(typ, None, None, ExtArray(
                        scala.Seq(CCInt.toSort), typ.toSort), ArrayLocation.Heap)
                    case _ => typ
                  }
                case _ => typ
              }
              val declaredVar =
                new CCVar(name, Some(getSourceInfo(argDec)), actualType, AutoStorage)
              scope.LocalVars addVar declaredVar

            case argDec : TypeHintAndParam =>
              val typ = getType(argDec.listdeclaration_specifier_)
              val actualType = argDec.declarator_ match {
                case _: BeginPointer if pointerArgs.nonEmpty => pointerArgs(ind)
                case p : BeginPointer => createHeapPointer(p, typ)
                case _ => typ
              }
              val declaredVar = new CCVar(getName(argDec.declarator_),
                                          Some(getSourceInfo(argDec)),
                                          actualType, AutoStorage)
              scope.LocalVars addVar declaredVar
              processHints(argDec.listannotation_)
//            case argDec : Abstract =>
          }
//      case dec : OldFuncDef =>
//        for (ident <- dec.listcident_)
//          scope.LocalVars += new ConstantTerm(ident)
      case dec : OldFuncDec =>
        // arguments are not specified ...
    }
    f.body
  }

  //////////////////////////////////////////////////////////////////////////////

  private object FunctionTranslator {
    def apply(functionName : String) =
      new FunctionTranslator(None, functionName)
    def apply(returnPred : CCPredicate, functionName : String) =
      new FunctionTranslator(Some(returnPred), functionName)
  }

  private class FunctionTranslator private (returnPred   : Option[CCPredicate],
                                            functionName : String) {

    private def symexFor(initPred : CCPredicate,
                         stm : Expression_stm) : (Symex, Option[CCTerm]) = {
      val exprSymex = Symex(symexContext, scope, initPred, heapModel)
      val res = stm match {
        case _ : SexprOne => None
        case stm : SexprTwo =>
          implicit val evalSettings = exprSymex.EvalSettings()
          implicit val evalContext = exprSymex.EvalContext()
                                              .withFunctionName(functionName)
          Some(exprSymex eval stm.exp_)
      }
      (exprSymex, res)
    }



    def translateNoReturn(compound : Compound_stm) : CCPredicate = {
      val finalPred = newPred(Nil, Some(getLastSourceInfo(compound)))
      translateWithEntryClause(compound, finalPred)
      postProcessClauses
      finalPred
    }

    def translateNoReturn(compound : Compound_stm,
                          entry : CCPredicate) : Unit = {
      val exitSrcInfo = Some(getLastSourceInfo(compound))
      val finalPred = newPred(Nil, exitSrcInfo)
      translate(compound, entry, finalPred)
      // add a default return edge
      val rp = returnPred.get
      output(addRichClause(Clause(atom(rp, scope.allFormalVarTerms take rp.arity),
                    List(atom(finalPred, scope.allFormalVarTerms  take finalPred.arity)),
                    true), exitSrcInfo))
      postProcessClauses
    }

    /**
     * The returned predicate is the predicate for the exit point for when
     * the function does not return with a `return` statement. This can happen,
     * for example, when a function is declared with a return type, but there
     * are paths out of the function without a `return` statement.
     * E.g., int main() { }
     */
    def translateWithReturn(compound : Compound_stm) : CCPredicate = {
      val finalPred = newPred(Nil, Some(getLastSourceInfo(compound)))
      translateWithEntryClause(compound, finalPred)
      // add a default return edge
      //val rp = returnPred.get
      //output(Clause(atom(rp, (scope.allFormalVars take (rp.arity - 1)) ++
      //                       List(IConstant(new ConstantTerm("__result")))),
      //              List(atom(finalPred, scope.allFormalVars)),
      //              true))
      postProcessClauses
      finalPred
    }

    def translateWithReturn(compound : Compound_stm,
                            entry : CCPredicate) : CCPredicate = {
      val finalPred = returnPred match {
          case Some(pred) => pred
          case None => newPred(Nil, Some(getLastSourceInfo(compound)))
      }
      translate(compound, entry, finalPred)
      // add a default return edge
      //val rp = returnPred.get
      //output(Clause(atom(rp, (scope.allFormalVars take (rp.arity - 1)) ++
      //                       List(IConstant(new ConstantTerm("__result")))),
      //              List(atom(finalPred, scope.allFormalVars)),
      //              true))
      postProcessClauses
      finalPred
    }

    ////////////////////////////////////////////////////////////////////////////

    private def postProcessClauses : Unit = {
      connectJumps
      mergeAtomicBlocks
    }

    private def connectJumps : Unit =
      for ((label, jumpPred, jumpVars, position, srcInfo) <- jumpLocs)
        (labelledLocs get label) match {
          case Some((targetPred, targetVars)) => {
            val commonVars =
              (jumpVars zip targetVars).takeWhile({
                case (x, y) => x == y
              }).map(_._1)
            val jumpArgs = commonVars ++ (
              for (i <- 0 until (jumpPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("preArg_" + i)))
            val targetArgs = commonVars ++ (
              for (i <- 0 until (targetPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("postArg_" + i)))
            val newClause = Clause(atom(targetPred, targetArgs),
                                   List(atom(jumpPred, jumpArgs)),
                                   true)
            addRichClause(newClause, Some(srcInfo))
            clauses(position) = (newClause,
                                 ParametricEncoder.NoSync)
            usedJumpTargets.put(targetPred, label)
          }
          case None =>
            throw new TranslationException("cannot goto label " + label)
        }

    private def mergeAtomicBlocks : Unit = if (!atomicBlocks.isEmpty) {
      val sortedBlocks =
        atomicBlocks sortWith { case ((s1, e1), (s2, e2)) =>
                                  s1 < s2 || (s1 == s2 && e1 > e2) }

      val offset = sortedBlocks.head._1
      var concernedClauses = clauses.slice(offset, clauses.size).toList
      reduceToSize(clauses, offset)

      var curPos = offset
      for ((bstart, bend) <- sortedBlocks)
        if (bstart >= curPos) {
          while (curPos < bend) {
            clauses += concernedClauses.head
            concernedClauses = concernedClauses.tail
            curPos = curPos + 1
          }
          mergeClauses(clauses.size - (bend - bstart))
        }

      clauses ++= concernedClauses

      val bodyPreds =
        (for ((c, _) <- clauses.iterator; p <- c.bodyPredicates.iterator)
         yield p).toSet

      for ((Clause(IAtom(pred, _), _, _), _) <- clauses.iterator)
        if (!(bodyPreds contains pred) &&
            (usedJumpTargets.exists(t => t._1.pred == pred)))
          throw new TranslationException(
            "cannot goto label" +
            usedJumpTargets.find(t => t._1.pred == pred).get._2 +
            "which was eliminated due to atomic blocks")
    }

    private val jumpLocs =
      new ArrayBuffer[(String, CCPredicate, scala.Seq[ITerm], Int, SourceInfo)]
    private val labelledLocs =
      new MHashMap[String, (CCPredicate, scala.Seq[ITerm])]
    private val usedJumpTargets =
      new MHashMap[CCPredicate, String]
    private val atomicBlocks =
      new ArrayBuffer[(Int, Int)]

    ////////////////////////////////////////////////////////////////////////////

    private def translate(stm : Stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit =
      stm match {
        case stm: LabelS =>
          translate(stm.labeled_stm_, entry, exit)
        case stm: CompS =>
          translate(stm.compound_stm_, entry, exit)
        case stm: ExprS =>
          val symex = symexFor(entry, stm.expression_stm_)._1
          symex outputClause(exit, exit.srcInfo)
        case stm: SelS =>
          translate(stm.selection_stm_, entry, exit)
        case stm: IterS =>
          translate(stm.iter_stm_, entry, exit)
        case stm: JumpS =>
          translate(stm.jump_stm_, entry, exit)
        case stm: AtomicS =>
          translate(stm.atomic_stm_, entry, exit)
        case stm: AnnotationS => // todo: move this into a separate translate method
          try{translate(stm.annotation_, entry)}
          catch {
            case e : Exception =>
              warn("Ignoring ACSL annotation (possibly " +
                "an error or an unsupported fragment):\n" + e.getMessage)
          }
        case stm : AnnotatedIterS =>
          translate(stm.annotation_, stm.iter_stm_, entry, exit)
      }

    private def translate(stm : Annotation, entry : CCPredicate) : Unit = {
      val annotationInfo = AnnotationParser(annotationStringExtractor(stm))
      annotationInfo match {
        case scala.Seq(MaybeACSLAnnotation(annot, _)) =>
          val stmSymex = Symex(symexContext, scope, entry, heapModel)
          class LocalContext extends ACSLTranslator.StatementAnnotationContext {
            /**
             * Returns the term from the init atom - this should work as
             * long as the annotation does not have side effects, because
             * it always returns the original terms from initAtom
             */
            override def getTermInScope(name: String): Option[CCTerm] = {
              entry.argVars.zipWithIndex.find {
                case (v, i) => v.name == name
              } match {
                case Some((v, i)) =>
                  stmSymex.initAtomArgs match {
                    case Some(args) => Some(CCTerm.fromTerm(args(i), v.typ, v.srcInfo))
                    case None => None
                  }
                case None => None
              }
            }

            override def getGlobals: scala.Seq[CCVar] = scope.GlobalVars.vars.toSeq
            override def sortWrapper(s: Sort): Option[IFunction] =
              sortWrapperMap get s
            override def sortGetter(s: Sort): Option[IFunction] =
              sortGetterMap get s
            override def wrapperSort(wrapper: IFunction): Option[Sort] =
              wrapper match {
                case w: MonoSortedIFunction => 
                  wrapperSortMap.get(w)
                case _ => None
              }
            override def getterSort(getter: IFunction): Option[Sort] =
              getter match {
                case g: MonoSortedIFunction => 
                  getterSortMap.get(g)
                case _ => None
              } 

            override def getCtor(s: Sort): Int = sortCtorIdMap(s)
            override def getTypOfPointer(t: CCType): CCType =
              t match {
                case p : CCHeapPointer => p.typ
                case t => t
              }
            override def isHeapEnabled: Boolean = modelHeap
            override def getHeap: HeapObj =
              if (modelHeap) heap
              else throw new TranslationException("getHeap called with no heap!")
            override def getHeapTerm: ITerm = {
              if (modelHeap) {
                val heapVar = heapModel.get match {
                  case m : HeapTheoryModel => m.heapVar
                  case _ => throw new TranslationException(
                    "Heap in ACSL only supported using the theory of heaps.")
                }
                stmSymex.getValues(scope.GlobalVars.lastIndexWhere(heapVar)).toTerm
              } else throw new TranslationException("getHeapTerm called with no heap!")
            }
            override def getOldHeapTerm: ITerm = {
              if (modelHeap) getHeapTerm
              else throw new TranslationException("getOldHeapTerm called with no heap!")
            } // todo: heap term for exit predicate?

            override val getStructMap: Map[IFunction, CCStruct] = 
              structDefs.values.map((struct: CCStruct) => (struct.ctor, struct)).toMap

            override val annotationBeginSourceInfo : SourceInfo =
              getSourceInfo(stm)

            override val annotationNumLines : Int = 1
          }
          ACSLTranslator.translateACSL(
            "/*@" + annot + "*/", new LocalContext()) match {
            case res: tricera.acsl.StatementAnnotation =>
              if (res.isAssert) {
                stmSymex.assertProperty(res.f, Some(getSourceInfo(stm)),
                                        properties.Reachability)
              } else
                warn("Ignoring annotation: " + annot)
            case _ => warn("Ignoring annotation: " + annot)
          }
        case _ => warn("Ignoring annotation: " + annotationInfo)
      }
    }

    private def translate(loop_annot : Annotation,
                          iter       : Iter_stm,
                          entry      : CCPredicate,
                          exit       : CCPredicate) : Unit = {
      val annotationInfo = AnnotationParser(annotationStringExtractor(loop_annot))
      annotationInfo match {
        case scala.Seq(MaybeACSLAnnotation(annot, _)) =>
          val stmSymex = Symex(symexContext, scope, entry, heapModel)
          class LocalContext extends ACSLTranslator.StatementAnnotationContext {
            /**
             * Returns the term from the init atom - this should work as
             * long as the annotation does not have side effects, because
             * it always returns the original terms from initAtom
             */
            override def getTermInScope(name : String) : Option[CCTerm] = {
              entry.argVars.zipWithIndex.find{
                case (v, i) => v.name == name
              } match {
                case Some((v, i)) =>
                  stmSymex.initAtomArgs match {
                    case Some(args) => Some(CCTerm.fromTerm(args(i), v.typ, v.srcInfo))
                    case None       => None
                  }
                case None         => None
              }
            }

            override def getGlobals : scala.Seq[CCVar] = scope.GlobalVars.vars.toSeq
            override def sortWrapper(s : Sort) : Option[IFunction] =
              sortWrapperMap get s
            override def sortGetter(s : Sort) : Option[IFunction] =
              sortGetterMap get s
            override def wrapperSort(wrapper: IFunction): Option[Sort] =
              wrapper match {
                case w: MonoSortedIFunction => 
                  wrapperSortMap.get(w)
                case _ => None
              }
            override def getterSort(getter: IFunction): Option[Sort] =
              getter match {
                case g: MonoSortedIFunction => 
                  getterSortMap.get(g)
                case _ => None
              } 
            override def getCtor(s : Sort) : Int = sortCtorIdMap(s)
            override def getTypOfPointer(t : CCType) : CCType =
              t match {
                case p : CCHeapPointer => p.typ
                case _ => t
              }
            override def isHeapEnabled : Boolean = modelHeap
            override def getHeap : HeapObj =
              if (modelHeap) heap else throw NeedsHeapModelException
            override def getHeapTerm : ITerm = {
              if (modelHeap) {
                val heapVar = heapModel.get match {
                  case m : HeapTheoryModel => m.heapVar
                  case _                   => throw new TranslationException(
                    "Heap in ACSL only supported using the theory of heaps.")
                }
                stmSymex.getValues(scope.GlobalVars.lastIndexWhere(heapVar)).toTerm
              } else throw NeedsHeapModelException
            }

            override def getOldHeapTerm : ITerm =
              getHeapTerm // todo: heap term for exit predicate?
            
            override val getStructMap: Map[IFunction, CCStruct] = 
              structDefs.values.map((struct: CCStruct) => (struct.ctor, struct)).toMap

            override val annotationBeginSourceInfo : SourceInfo =
              getSourceInfo(loop_annot)

            override val annotationNumLines : Int = 1
          }
          ACSLTranslator.translateACSL(
            "/*@" + annot + "*/", new LocalContext()) match {
            case res : tricera.acsl.LoopAnnotation =>
                ???
            case _ =>
              warn("Ignoring annotation: " + annot)
              ???
          }
        case _  =>
          warn("Ignoring annotation: " + annotationInfo)
          ???
      }
    }


    private def translate(dec : Dec, entry : CCPredicate) : CCPredicate = {
      val decSymex = Symex(symexContext, scope, entry, heapModel)
      collectVarDecls(dec, false, decSymex, "", false)
      val exit = newPred(Nil, Some(getSourceInfo(dec)))
      decSymex outputClause(exit, exit.srcInfo)
      exit
    }

    private def translate(stm : Labeled_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = stm match {
      case stm : SlabelOne => { // Labeled_stm ::= CIdent ":" Stm ;
        if (labelledLocs contains stm.cident_)
          throw new TranslationException("multiple labels " + stm.cident_)
        labelledLocs.put(stm.cident_, (entry, scope.allFormalVarTerms))
        translate(stm.stm_, entry, exit)
      }
      case stm : SlabelTwo => { // Labeled_stm ::= "case" Constant_expression ":" Stm ;
        val caseVal = translateConstantExpr(stm.constant_expression_)
        innermostSwitchCaseCollector += ((caseVal, entry))
        translate(stm.stm_, entry, exit)
      }
      case stm : SlabelThree => { // . Labeled_stm ::= "default" ":" Stm;
        innermostSwitchCaseCollector += ((null, entry))
        translate(stm.stm_, entry, exit)
      }
    }

    private def translateWithEntryClause(
                          compound : Compound_stm,
                          exit : CCPredicate) : Unit = compound match {
      case compound : ScompOne =>
        output(addRichClause(Clause(atom(exit, scope.allVarInits take exit.arity),
                                    List(), globalPreconditions),
          Some(getSourceInfo(compound)))
        )
      case compound : ScompTwo => {
        scope.LocalVars pushFrame

        val stmsIt = ap.util.PeekIterator(compound.liststm_.asScala.toSeq.iterator)

        // merge simple side-effect-free declarations with
        // the entry clause
        var entryPred = newPred(Nil,
          if(stmsIt.hasNext) Some(getSourceInfo(stmsIt.peekNext)) else None)
        var entryClause =
          Clause(atom(entryPred, scope.allVarInits take entryPred.arity), List(), globalPreconditions)

        while (stmsIt.hasNext && isSEFDeclaration(stmsIt.peekNext)) {
          val decSymex = Symex(symexContext, scope, entryPred, heapModel)
          collectVarDecls(stmsIt.next.asInstanceOf[DecS].dec_,
                          false, decSymex, "", false)
          val srcInfo = entryPred.srcInfo // todo: correct srcInfo?
          entryPred = newPred(Nil,
            if(stmsIt.hasNext) Some(getSourceInfo(stmsIt.peekNext)) else None) // todo: correct?
          entryClause = merge((decSymex genClause(entryPred, srcInfo)).clause, entryClause)
        }
        output(addRichClause(entryClause, entryPred.srcInfo))

        val initStmts : Iterator[Stm] = {
          val inputInitCode = scala.Seq()

          val heapModelInitCode =
            if (modelHeap) heapModelFactory.getInitCodeToInject else scala.Seq()

          (inputInitCode ++ heapModelInitCode).iterator.map { code =>
            ParseUtil.parseStatement(new java.io.StringReader(code))
          }
        }

        translateStmSeq(ap.util.PeekIterator(initStmts ++ stmsIt), entryPred, exit)
        scope.LocalVars popFrame
      }
    }

    private def isSEFDeclaration(stm : Stm) : Boolean = stm match {
      case stm: DecS => {
        collectVarDecls(stm.dec_, isGlobal = false).forall {
          case v : CCVarDeclaration if v.needsHeap => false
          case v : CCVarDeclaration =>
            v.maybeInitializer match {
              case Some(initializer) if v.hints.nonEmpty =>
                initializer.asInstanceOf[InitExpr].exp_ match {
                  case _ : Econst => true
                  case _ => false
                }
              case Some(initializer) => isSEFInitializer(initializer)
              case None => true
            }
          case _ => true
        }
      }
      case _ => false
    }

    private def isSEFInitializer(inits: Initializers) : Boolean =
      inits match {
        case init : AnInit => isSEFInitializer(init.initializer_)
        case init : MoreInit => isSEFInitializer(init.initializer_) &&
                                isSEFInitializer(init.initializers_)
      }
    private def isSEFInitializer(init: Initializer) : Boolean =
      init match {
        case decl: InitExpr => decl.exp_ match {
          case _ : Econst => true
          case _ => false
        }
        case _ : InitListOne | _ : InitListTwo =>
          val inits = init match {
            case decl : InitListOne => decl.initializers_
            case decl : InitListTwo => decl.initializers_
          }
          isSEFInitializer(inits)
      }

    private def translate(compound : Compound_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = compound match {
      case compound : ScompOne => {
        val vars = scope.allFormalVarTerms
        output(addRichClause(Clause(atom(exit, vars take exit.arity),
                                    List(atom(entry, vars take entry.arity)), true),
          Some(getSourceInfo(compound))))
      }
      case compound : ScompTwo => {
        scope.LocalVars pushFrame

        val stmsIt = compound.liststm_.asScala.toSeq.iterator
        translateStmSeq(stmsIt, entry, exit)
        scope.LocalVars popFrame
      }
    }

    private def translateStmSeq(stmsIt : Iterator[Stm],
                                entry : CCPredicate,
                                exit : CCPredicate) : Unit = {
      var prevPred = entry
      while (stmsIt.hasNext)
        stmsIt.next match {
          case stm : DecS => {
            val srcInfo = Some(getSourceInfo(stm))
            prevPred = translate(stm.dec_, prevPred)
            if (!stmsIt.hasNext) {
              output(addRichClause(Clause(
                atom(exit, scope.allFormalVarTerms take exit.arity),
                List(atom(prevPred, scope.allFormalVarTerms take prevPred.arity)),
                true), srcInfo))
            }
          }
          case stm => {
            val srcInfo = Some(getSourceInfo(stm))
            val nextPred = if (stmsIt.hasNext) newPred(Nil, None) // todo: line no?
                           else exit
            translate(stm, prevPred, nextPred)
            prevPred = nextPred
          }
        }
    }

    type SwitchCaseCollector = ArrayBuffer[(CCTerm, CCPredicate)]

    var innermostLoopCont : CCPredicate = null
    var innermostLoopExit : CCPredicate = null
    var innermostSwitchCaseCollector : SwitchCaseCollector = null

    private def withinLoop[A](
                     loopCont : CCPredicate, loopExit : CCPredicate)
                     (comp : => A) : A = {
      val oldCont = innermostLoopCont
      val oldExit = innermostLoopExit
      innermostLoopCont = loopCont
      innermostLoopExit = loopExit
      try {
        comp
      } finally {
        innermostLoopCont = oldCont
        innermostLoopExit = oldExit
      }
    }

    private def withinSwitch[A](
                     switchExit : CCPredicate,
                     caseCollector : SwitchCaseCollector)
                     (comp : => A) : A = {
      val oldExit = innermostLoopExit
      val oldCollector = innermostSwitchCaseCollector
      innermostLoopExit = switchExit
      innermostSwitchCaseCollector = caseCollector
      try {
        comp
      } finally {
        innermostLoopExit = oldExit
        innermostSwitchCaseCollector = oldCollector
      }
    }

    private def translate(stm : Iter_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = stm match {
      case stm : SiterOne => {
        // while loop

        val first = newPred(Nil, entry.srcInfo)

        if (TriCeraParameters.get.inferLoopInvariants)
          addLoopInvariant(entry, getSourceInfo(stm))
        val condSymex = Symex(symexContext, scope, entry, heapModel)
        implicit val evalSettings = condSymex.EvalSettings()
        implicit val evalContext = condSymex.EvalContext()
                                            .withFunctionName(functionName)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, first, exit, entry.srcInfo)
        withinLoop(entry, exit) {
          translate(stm.stm_, first, entry)
        }
      }

      case stm : SiterTwo => {
        // do ... while loop

        val srcInfo = Some(getSourceInfo(stm))
        val first = newPred(Nil, srcInfo)

        if (TriCeraParameters.get.inferLoopInvariants)
          addLoopInvariant(first, srcInfo.get)

        withinLoop(first, exit) {
          translate(stm.stm_, entry, first)
        }

        val condSymex = Symex(symexContext, scope, first, heapModel)
        implicit val evalSettings = condSymex.EvalSettings()
        implicit val evalContext  = condSymex.EvalContext()
                                             .withFunctionName(functionName)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, entry, exit, srcInfo)
      }

      case _ : SiterThree | _ : SiterFour => {
        // for loop

        val srcInfo = Some(getSourceInfo(stm))
        val first, second, third = newPred(Nil, srcInfo) // todo: line no might not be correct

        val (initStm, condStm, body) = stm match {
          case stm : SiterThree =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
          case stm : SiterFour  =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
        }

        if (TriCeraParameters.get.inferLoopInvariants)
          addLoopInvariant(first, srcInfo.get)

        symexFor(entry, initStm)._1 outputClause(first, srcInfo)

        val (condSymex, condExpr) = symexFor(first, condStm)
        val cond : IFormula = condExpr match {
          case Some(expr) => expr.toFormula
          case None       => true
        }

        condSymex.outputITEClauses(cond, second, exit, srcInfo)

        import HornClauses._
        withinLoop(third, exit) {
          translate(body, second, third)
        }

        stm match {
          case stm : SiterThree =>
            output(addRichClause(
              first(scope.allFormalVars) :- third(scope.allFormalVarTerms), srcInfo))
          case stm : SiterFour  => {
            val incSymex = Symex(symexContext, scope, third, heapModel)
            val evalContext = incSymex.EvalContext()
                                               .withFunctionName(functionName)
            incSymex.eval(stm.exp_)(incSymex.EvalSettings(), evalContext)
            incSymex outputClause (first, srcInfo)
          }
        }
      }
    }

    private def translate(stm : Selection_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = stm match {
      case _ : SselOne | _ : SselTwo => { // if
        val condSymex = Symex(symexContext, scope, entry, heapModel)
        implicit val evalSettings = condSymex.EvalSettings()
        implicit val evalContext = condSymex.EvalContext()
                                            .withFunctionName(functionName)
        val (cond, srcInfo1, srcInfo2) = stm match {
          case stm : SselOne =>
            ((condSymex eval stm.exp_).toFormula,
              Some(getSourceInfo(stm)), Some(getSourceInfo(stm)))
          case stm : SselTwo =>
            ((condSymex eval stm.exp_).toFormula,
              Some(getSourceInfo(stm.stm_1)), Some(getSourceInfo(stm.stm_2)))
        }
        val first = newPred(Nil, srcInfo1)
        val second = newPred(Nil, srcInfo2)
        val vars = scope.allFormalVarTerms

        condSymex.outputITEClauses(cond, first, second, srcInfo2) // todo: correct line no?
        stm match {
          case stm : SselOne => {
            translate(stm.stm_, first, exit)
            output(addRichClause(
              Clause(atom(exit, vars take exit.arity),
                     List(atom(second, vars take second.arity)), true),
              srcInfo1)) // todo: correct line no?
          }
          case stm : SselTwo => {
            translate(stm.stm_1, first, exit)
            translate(stm.stm_2, second, exit)
          }
        }
      }

      case stm : SselThree => {  // switch
        import IExpression._
        val selectorSymex = Symex(symexContext, scope, entry, heapModel)
        implicit val evalSettings = selectorSymex.EvalSettings()
        implicit val evalContext  = selectorSymex.EvalContext()
                                                 .withFunctionName(functionName)
        val selector = (selectorSymex eval stm.exp_).toTerm

        val newEntry = newPred(Nil, Some(getSourceInfo(stm)))
        val collector = new SwitchCaseCollector

        withinSwitch(exit, collector) {
          translate(stm.stm_, newEntry, exit)
        }

        // add clauses for the various cases of the switch
        val (defaults, cases) = collector partition (_._1 == null)
        val guards = for ((value, _) <- cases) yield (selector === value.toTerm)

        for (((_, target), guard) <- cases.iterator zip guards.iterator) {
          selectorSymex.saveState
          selectorSymex addGuard guard
          selectorSymex outputClause(target, target.srcInfo) // todo: correct line no?
          selectorSymex.restoreState
        }

        defaults.toSeq match {
          case scala.Seq() =>
            // add an assertion that we never try to jump to a case that
            // does not exist. TODO: add a parameter for this?
            selectorSymex assertProperty(
              or(guards), Some(getSourceInfo(stm)),
              properties.SwitchCaseValidJump)
          case scala.Seq((_, target)) => {
            selectorSymex.saveState
            selectorSymex addGuard ~or(guards)
            selectorSymex outputClause(target, target.srcInfo)
            selectorSymex.restoreState
          }
          case _ =>
            throw new TranslationException("multiple default cases in switch")
        }
      }
    }

    private def translate(jump : Jump_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = {
      val srcInfo = Some(getSourceInfo(jump)) // todo: correct line no?
      jump match {
        case jump : SjumpOne   => { // goto
          jumpLocs += ((jump.cident_, entry, scope.allFormalVarTerms, clauses.size,
            getSourceInfo(jump)))
          // reserve space for the later jump clause
          output(new CCClause(null, null))
        }
        case jump : SjumpTwo   => { // continue
          if (innermostLoopCont == null)
            throw new TranslationException(
              "\"continue\" can only be used within loops")
          Symex(symexContext, scope, entry, heapModel).outputClause(innermostLoopCont, srcInfo)
        }
        case jump : SjumpThree => { // break
          if (innermostLoopExit == null)
            throw new TranslationException(
              "\"break\" can only be used within loops")
          Symex(symexContext, scope, entry, heapModel).outputClause(innermostLoopExit, srcInfo)
        }
        case jump : SjumpFour  => // return
          returnPred match {
            case Some(rp) => {
              var nextPred = entry
              val args     = scope.allFormalVarTerms take rp.arity
              output(addRichClause(Clause(atom(rp, args),
                                          List(atom(nextPred, scope.allFormalVarTerms take nextPred.arity)),
                                          true), srcInfo))
            }
            case None     =>
              throw new TranslationException(
                "\"return\" can only be used within functions")
          }
        case jump : SjumpFive  => { // return exp
          val symex = Symex(symexContext, scope, entry, heapModel)
          implicit val evalSettings = symex.EvalSettings()
          implicit val evalContext  = symex.EvalContext()
                                           .withFunctionName(functionName)
          val retValue = symex eval jump.exp_
          if (retValue.typ.isInstanceOf[CCStackPointer]) {
            throw new UnsupportedCFragmentException(
              "Returning stack pointers from functions is not yet supported.")
          }
          returnPred match {
            case Some(rp) =>
              val args = (symex.getValuesAsTerms take(rp.arity - 1)) ++
                         List(retValue.toTerm)
              symex outputClause(atom(rp, args), srcInfo)
            case None     =>
              throw new TranslationException(
                "\"return\" can only be used within functions")
          }
        }
      }
    }

    private def translate(aStm : Atomic_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = {
      val srcInfo = Some(getSourceInfo(aStm))
      aStm match {
        case stm : SatomicOne => {
          val srcInfo = Some(getSourceInfo(stm))
          val currentClauseNum = clauses.size
          inAtomicMode {
            // add a further state inside the block, to correctly
            // distinguish between loops within the block, and a loop
            // around the block
            val first = newPred(Nil, srcInfo)
            val entrySymex = Symex(symexContext, scope, entry, heapModel)
            entrySymex outputClause(first, srcInfo)
            translate(stm.stm_, first, exit)
          }
          atomicBlocks += ((currentClauseNum, clauses.size))
        }
        case stm : SatomicTwo => {
          val currentClauseNum = clauses.size
          inAtomicMode {
            val first = newPred(Nil, srcInfo)
            val condSymex = Symex(symexContext, scope, entry, heapModel)
            implicit val evalSettings = condSymex.EvalSettings()
            implicit val evalContext  = condSymex.EvalContext()
                                                 .withFunctionName(functionName)
            condSymex.saveState
            val cond = (condSymex eval stm.exp_).toFormula
            if (!condSymex.atomValuesUnchanged)
              throw new TranslationException(
                "expressions with side-effects are not supported in \"within\"")
            import HornClauses._
            timeInvariants +=
              (cond :- atom(entry, scope.allFormalVarTerms take entry.arity))
            condSymex outputClause(first, srcInfo)
            translate(stm.stm_, first, exit)
          }
          atomicBlocks += ((currentClauseNum, clauses.size))
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val system : ParametricEncoder.System = {
    translateProgram

    val singleThreaded =
      processes.size == 1 &&
      processes.head._2 == ParametricEncoder.Singleton

    val predHints =
      (for (p <- ParametricEncoder.allPredicates(processes.toSeq).iterator;
            maybePreds = predicateHints get p;
            if maybePreds.isDefined;
            if (!maybePreds.get.isEmpty))
       yield (p -> maybePreds.get.toList)).toMap

    val backgroundClauses =
      (for ((_, clauses) <- functionClauses.toSeq.sortBy(_._1);
            c <- clauses) yield c._1) ++
      (for ((_, clauses) <- functionAssertionClauses.toSeq.sortBy(_._1);
            c <- clauses) yield c.clause)
    val backgroundPreds =
      (for (c <- backgroundClauses;
           p <- c.predicates.toSeq.sortBy(_.name);
           if p != HornClauses.FALSE)
      yield p) ++ uninterpPredDecls.values.map(_.pred)

    val backgroundAxioms =
      if (backgroundPreds.isEmpty && backgroundClauses.isEmpty)
        ParametricEncoder.NoBackgroundAxioms
      else
        ParametricEncoder.SomeBackgroundAxioms(backgroundPreds,
                                               backgroundClauses)

    ParametricEncoder.System(processes.toList,
                             if (singleThreaded) {
                               if (useTime) 2 else 0 // todo : anything for heap here? why only 2 if useTime?
                             } else {
                               scope.GlobalVars.size
                             },
                             None,
                             if (useTime)
                               ParametricEncoder.ContinuousTime(0, 1)
                             else
                               ParametricEncoder.NoTime,
                             timeInvariants.toSeq,
                             (assertionClauses).map(_.clause).toList,
                             VerificationHints(predHints),
                             backgroundAxioms,
                             otherPredsToKeep =
                               loopInvariants.map(_._2._1.pred).toList)
  }

  def getRichClause(clause : Clause) : Option[CCClause] = {
    clauseToRichClause.values.find(richClause =>
      richClause.clause == clause ||
      richClause.clause.constraint == clause.constraint &&
        richClause.clause.head.pred == clause.head.pred &&
        (richClause.clause.body.size == clause.body.length) &&
        (richClause.clause.body zip clause.body).forall(pair =>
          pair._1.pred == pair._2.pred)
    )
  }

  object PredPrintContext extends ReaderMain.PredPrintContext {
    private def getPred (pred : Predicate) : CCPredicate = {
      predCCPredMap get pred match {
        case Some(ccPred) => ccPred
        case None => predCCPredMap find
          (p => Literals.invPrefix + p._1.name == pred.name) match {
          case Some(v) => v._2
          case None => throw new TranslationException("Could not find pred: " +
            pred)
        }
      }
    }
    def predWithArgNames (pred : Predicate) : String =
      getPred(pred).toString
    def predWithArgNamesAndLineNumbers (pred : Predicate) : String =
      getPred(pred).toStringWithLineNumbers
    def predArgNames (pred : Predicate) : scala.Seq[String] =
      getPred(pred).argVars.map(_.toString).toSeq
    def predSrcInfo (pred : Predicate) : Option[SourceInfo] =
      getPred(pred).srcInfo
    def isUninterpretedPredicate (predicate : Predicate) : Boolean =
      uninterpPredDecls.values.exists(ccPred => ccPred.pred == predicate)
  }
}
