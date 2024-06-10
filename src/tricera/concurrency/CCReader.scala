/**
 * Copyright (c) 2015-2024 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
import ap.theories.{ADT, ExtArray, Heap, ModuloArithmetic}
import ap.types.{MonoSortedIFunction, MonoSortedPredicate, SortedConstantTerm}
import concurrent_c._
import concurrent_c.Absyn._
import hornconcurrency.ParametricEncoder
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintInitPred, VerifHintTplElement, VerifHintTplEqTerm, VerifHintTplPred}
import lazabs.horn.bottomup.HornClauses
import IExpression.{ConstantTerm, Predicate, Sort, toFunApplier}

import scala.collection.mutable.{ArrayBuffer, Buffer, Stack, HashMap => MHashMap, HashSet => MHashSet}
import tricera.Util._
import tricera.acsl.{ACSLTranslator, FunctionContract}
import tricera.concurrency.ccreader._
import tricera.concurrency.ccreader.CCBinaryExpressions._
import tricera.params.TriCeraParameters
import tricera.parsers.AnnotationParser
import tricera.parsers.AnnotationParser._
import CCExceptions._
import tricera.{Util, properties}

object CCReader {
  private[concurrency] var useTime = false
  private[concurrency] var modelHeap = false

  // Reserve two variables for time
  private[concurrency] val GT  = new CCVar("_GT", None, CCClock, GlobalStorage)
  private[concurrency] val GTU = new CCVar("_GTU", None, CCInt, GlobalStorage)

  def apply(input : java.io.Reader, entryFunction : String,
            propertiesToCheck : Set[properties.Property] = Set(
              properties.Reachability))
  : (CCReader, Boolean) = { // second ret. arg is true if modelled heap
    def entry(parser : concurrent_c.parser) = parser.pProgram
    val prog = parseWithEntry(input, entry _)
//    println(printer print prog)

    var reader : CCReader = null
    while (reader == null)
      try {
        reader = new CCReader(prog, entryFunction, propertiesToCheck)
      } catch {
        case NeedsTimeException => {
          warn("enabling time")
          useTime = true
        }
        case NeedsHeapModelException => {
          modelHeap = true
        }
      }
    (reader, modelHeap)
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

  val heapTermName = "@h"

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

  // a wrapper for IExpression.Predicate that keeps more info about arguments
  case class CCPredicate(pred : Predicate, argVars : Seq[CCVar],
                         srcInfo : Option[SourceInfo]) {
    import ap.parser.ITerm
    import IExpression._
    def apply(terms : Seq[ITerm]) = pred(terms: _*)
    def apply[X: scala.reflect.ClassTag](ccVars : Seq[CCVar]) =
      pred(ccVars.map(_.term): _*)
    def arity : Int = pred.arity
    override def toString: String =
      pred.name + (if(argVars.nonEmpty) "(" + argVars.mkString(", ") + ")" else "")
    def toStringWithLineNumbers: String =
      pred.name + (if(argVars.nonEmpty) "(" +
        argVars.map(_.toStringWithLineNumbers).mkString(", ") + ")" else "")
    assert(pred.arity == argVars.size)
  }

  class FunctionContext (val prePred  : CCPredicate,
                         val postPred : CCPredicate,
                         val acslContext : ACSLTranslator.FunctionContext,
                         val prePredACSLArgNames : Seq[String],
                         val postPredACSLArgNames : Seq[String])

}

////////////////////////////////////////////////////////////////////////////////

class CCReader private (prog              : Program,
                        entryFunction     : String,
                        propertiesToCheck : Set[properties.Property]) {

  import CCReader._

  private val printer = new PrettyPrinterNonStatic

  //////////////////////////////////////////////////////////////////////////////

  private implicit def toRichExpr(expr : CCExpr) :
    Object{def mapTerm(m:ITerm => ITerm) : CCExpr} = new Object {
    def mapTerm(m : ITerm => ITerm) : CCExpr =
    // TODO: type promotion when needed
    CCTerm(expr.typ cast m(expr.toTerm), expr.typ, expr.srcInfo)
  }

  //////////////////////////////////////////////////////////////////////////////

  import HornClauses.Clause

  private val predCCPredMap = new MHashMap[Predicate, CCPredicate]

  private sealed class CCVars {
    val vars = new ArrayBuffer[CCVar]
    def addVar (v : CCVar) : Int = {
      vars += v
      size - 1
    }
    def size : Int = vars.size
    def lastIndexWhere(name : String, enclosingFunction : String) =
      vars lastIndexWhere(v => v.name == name &&
        (!v.isStatic || v.enclosingFunctionName.get == enclosingFunction))
    def lastIndexWhere(v : CCVar) = vars lastIndexWhere(_ == v)
    def contains (c : ConstantTerm) = vars exists (_.term == c)
    def iterator = vars.iterator
    def formalVars = vars.toList
    def formalVarTerms = vars.map(_.term).toList
    def formalTypes = vars.map(_.typ).toList
  }

  private object GlobalVars extends CCVars {
    val inits = new ArrayBuffer[CCExpr]
  }
  private object LocalVars extends CCVars {
    val frameStack = new Stack[Int]

    override def addVar (v : CCVar) : Int = {
      variableHints += List()
      super.addVar(v)
    }
    def update(idx : Int, elem : CCVar) {
      vars.update(idx, elem)
    }
    def pop(n : Int) = {
      LocalVars trimEnd n
      variableHints trimEnd n
      assert(variableHints.size == size + GlobalVars.size)
    }

    def lastOption : Option[CCVar] = vars.lastOption
    def last : CCVar = vars.last
    def remove(n : Int): CCVar = {
      assume(n >= 0 && n < size)
      variableHints.remove(n + GlobalVars.size)
      vars.remove(n)
    }
    def trimEnd(n: Int) = vars trimEnd n
    def pushFrame = frameStack push size
    def popFrame = {
      val newSize = frameStack.pop
      vars reduceToSize newSize
      variableHints reduceToSize (GlobalVars.size + newSize)
    }
    def getVarsInTopFrame : List[CCVar] =
      (vars takeRight (vars.size - frameStack.last)).toList
  }

  private def updateVarType(name : String, newType : CCType,
                            enclosingFunction : String) = {
    val ind = lookupVar(name, enclosingFunction)
    if (ind < GlobalVars.size) {
      val oldVar = GlobalVars.vars(ind)
      GlobalVars.vars(ind) =
        new CCVar(name, oldVar.srcInfo, newType, oldVar.storage)
    } else {
      val oldVar = LocalVars.vars(ind - GlobalVars.size)
      LocalVars.vars(ind - GlobalVars.size) =
        new CCVar(name, oldVar.srcInfo, newType, oldVar.storage)
    }
  }

  private var globalPreconditions : IFormula = true

  private def lookupVarNoException(name : String, enclosingFunction : String)
  : Int = {
    /**
     * @note Usage of `lastIndexWhere` is important for shadowing semantics.
     *       For the same reason, it is important to add static variables,
     *       which are stored as globals, after the globals.
     *       Note that static variables should only be accessible from
     *       enclosing functions where they were declared in.
     */
    LocalVars.lastIndexWhere(name, enclosingFunction) match {
      case -1 => GlobalVars.lastIndexWhere(name, enclosingFunction)
      case i  => i + GlobalVars.size
    }
  }

  private def lookupVar(name : String, enclosingFunction : String) : Int = {
    val actualName =
      if (TriCeraParameters.get.showVarLineNumbersInTerms) {
        name.lastIndexOf(CCVar.lineNumberPrefix) match {
            case -1 => name
            case i => name.take(i)
          }
      } else name
    lookupVarNoException(actualName, enclosingFunction) match {
      case -1 =>
        actualName match {
          case `heapTermName` if !modelHeap => throw NeedsHeapModelException
          case _ => throw new TranslationException(
            "Symbol " + actualName + " is not declared")
        }
      case i => i
    }
  }

  private def allFormalVars : Seq[CCVar] =
    GlobalVars.formalVars ++ LocalVars.formalVars
  private def allFormalVarTerms : Seq[ITerm] =
    GlobalVars.formalVarTerms ++ LocalVars.formalVarTerms
  private def allFormalVarTypes : Seq[CCType] =
    GlobalVars.formalTypes ++ LocalVars.formalTypes

  private def allFormalExprs : Seq[CCExpr] =
    ((for (v <- GlobalVars.iterator)
      yield CCTerm(v.term, v.typ, v.srcInfo)) ++
     (for (v <- LocalVars.iterator)
      yield CCTerm(v.term, v.typ, v.srcInfo))).toList
  private def allVarInits : Seq[ITerm] =
    (GlobalVars.inits.toList map (_.toTerm)) ++
      (LocalVars.formalVarTerms map (IExpression.i(_)))

  private def freeFromGlobal(t : IExpression) : Boolean =
    !ContainsSymbol(t, (s:IExpression) => s match {
                      case IConstant(c) => GlobalVars contains c // todo: true only with concurrency?
                      case _ => false
                    })

  private def freeFromGlobal(t : CCExpr) : Boolean = t match {
    case CCTerm(s, _, _) =>    freeFromGlobal(s)
    case CCFormula(f, _, _) => freeFromGlobal(f)
  }

  private val variableHints =
    new ArrayBuffer[Seq[VerifHintElement]]
  private var usingInitialPredicates = false

  //////////////////////////////////////////////////////////////////////////////

  private var tempVarCounter = 0
  private val evalVars = new MHashSet[String]

  private def getFreshEvalVar (typ     : CCType,
                               srcInfo : Option[SourceInfo],
                               name    : String = "",
                               storage : VariableStorage = AutoStorage) : CCVar = {
    val varName = {
      if (name.nonEmpty) {
        name
      } else {
        val prelName = "__eval" + (srcInfo match {
          case Some(info) => info.line.toString
          case None => ""
        })
        if (evalVars contains prelName) {
          tempVarCounter += 1
          prelName + "_" + tempVarCounter
        } else {
          evalVars += prelName
          prelName
        }
      }
    }

    val res = new CCVar(varName, srcInfo, typ, storage)
    res
  }


  //////////////////////////////////////////////////////////////////////////////

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  private val functionDefs  = new MHashMap[String, Function_def]
  private val functionDecls = new MHashMap[String, (Direct_declarator, CCType)]
  private val functionContexts = new MHashMap[String, FunctionContext]
  private val functionPostOldArgs = new MHashMap[String, Seq[CCVar]]
  private val functionClauses =
    new MHashMap[String, Seq[(Clause, ParametricEncoder.Synchronisation)]]
  private val functionAssertionClauses = new MHashMap[String, Seq[CCAssertionClause]]
  private val uniqueStructs = new MHashMap[Unique, String]
  private val structInfos   = new ArrayBuffer[StructInfo]
  private val structDefs    = new MHashMap[String, CCStruct]
  private val enumDefs      = new MHashMap[String, CCType]
  private val enumeratorDefs= new MHashMap[String, CCExpr]

  private val uninterpPredDecls     = new MHashMap[String, CCPredicate]
  private val interpPredDefs        = new MHashMap[String, CCFormula]
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

    clauses reduceToSize from

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
              args : Seq[CCVar],
              srcInfo : Option[SourceInfo]) : CCPredicate = {
    val pred = MonoSortedPredicate(name, args map (_ sort))
    val ccPred = CCPredicate(pred, args, srcInfo)
    predCCPredMap.put(pred, ccPred)
    ccPred
  }

  private def newPred(extraArgs : Seq[CCVar],
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
    val res = newPred(predName, allFormalVars ++ extraArgs, srcInfo)

    val hints = for (s <- variableHints; p <- s) yield p
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

    predicateHints.put(res.pred, allHints)
    res
  }

  private val predicateHints =
    new MHashMap[Predicate, Seq[VerifHintElement]]

  //////////////////////////////////////////////////////////////////////////////

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  //////////////////////////////////////////////////////////////////////////////

  if (useTime) {
    GlobalVars addVar GT
    GlobalVars.inits += CCTerm(GT.term, CCClock, None)
    GlobalVars addVar GTU
    GlobalVars.inits += CCTerm(GTU.term, CCInt, None)
    variableHints += List()
    variableHints += List()
  }

  private def collectStructDefsFromComp (comp : Compound_stm): Unit = {
    comp match {
      case        _: ScompOne =>
      case compound: ScompTwo =>
        val stmsIt = ap.util.PeekIterator(compound.liststm_.iterator)
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
                  f.listannotation_)
        case f : AnnotatedFunc =>
          FuncDef(f.compound_stm_, f.declarator_,
                  getSourceInfo(f),
                  Some(f.listdeclaration_specifier_),
                  f.listannotation_)
      }
    }
  }
  case class FuncDef(body : Compound_stm,
                     decl : Declarator,
                     sourceInfo : SourceInfo,
                     declSpecs : Option[ListDeclaration_specifier] = None,
                     annotations : Seq[Annotation]) {
    val name : String = getName(decl)
  }

  for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
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

  def defObjCtor(objectCtors : Seq[IFunction],
                 heapADTs : ADT) : ITerm = {
    objectCtors.last()
  }

  val ObjSort = HeapObj.ADTSort(0)

  val structCtorSignatures : List[(String, HeapObj.CtorSignature)] =
    (for ((struct, i) <- structInfos zipWithIndex) yield {
      if(struct.fieldInfos isEmpty) warn(
        s"Struct ${struct.name} was declared, but never defined, " +
          "or it has no fields.")
      val ADTFieldList : Seq[(String, HeapObj.CtorArgSort)] =
        for(FieldInfo(rawFieldName, fieldType, ptrDepth) <-
              struct.fieldInfos) yield
          (CCStruct.rawToFullFieldName(struct.name, rawFieldName),
            if (ptrDepth > 0) Heap.AddressCtor
            else { fieldType match {
              case Left(ind) => HeapObj.ADTSort(ind + 1)
              case Right(typ) =>
                typ match {
                  case _ : CCHeapArrayPointer => HeapObj.AddressRangeCtor
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
         ("O_Addr", HeapObj.CtorSignature(List(("getAddr", HeapObj.AddressCtor)), ObjSort)),
         ("O_AddrRange", HeapObj.CtorSignature(List(("getAddrRange", HeapObj.AddressRangeCtor)), ObjSort))
    )

  val wrapperSignatures : List[(String, HeapObj.CtorSignature)] =
    predefSignatures ++
      (for ((name, signature) <- structCtorSignatures) yield {
        ("O_" + name,
          HeapObj.CtorSignature(List(("get" + name, signature.result)), ObjSort))
      })

  val heap = new Heap("Heap", "Addr", ObjSort,
    List("HeapObject") ++ structCtorSignatures.unzip._1,
    wrapperSignatures ++ structCtorSignatures ++
      List(("defObj", HeapObj.CtorSignature(List(), ObjSort))),
    defObjCtor)

  private val heapVar = new CCVar(heapTermName, None, CCHeap(heap), GlobalStorage)
  val heapTerm = heapVar.term

  if (modelHeap) {
    GlobalVars addVar heapVar
    GlobalVars.inits += CCTerm(heapTerm, CCHeap(heap), None)
    variableHints += List()
  }

  /**
   * For checking [[properties.MemValidCleanup]], a prophecy variable is used.
   */
  private val memCleanupProphecyVar =
    new CCVar("@v_cleanup", None, CCHeapPointer(heap, CCVoid), GlobalStorage)
  if ((propertiesToCheck contains properties.MemValidCleanup) ||
      propertiesToCheck.contains(properties.MemValidTrack) &&
       TriCeraParameters.get.useMemCleanupForMemTrack) {
    GlobalVars addVar memCleanupProphecyVar
    GlobalVars.inits += CCTerm(heap.nullAddr(), memCleanupProphecyVar.typ, None)
    variableHints += List()
  }

  /**
   * It is important that globalExitPred has arguments for the ghost variables
   * and the heap - for instance we want to check that memory is cleaned before
   * exit, and it cannot be done if the prophecy variable does not exist at
   * that point. This is reachable, for instance, with the `abort` statement.
   */
  private val globalExitPred = newPred("exit", allFormalVars, None)

  private val structCtorsOffset = predefSignatures.size
  val defObj = heap.userADTCtors.last
  val structCount = structInfos.size
  val objectWrappers = heap.userADTCtors.take(structCount+structCtorsOffset)
  val objectGetters =
    for (sels <- heap.userADTSels.take(structCount+structCtorsOffset)
         if sels.nonEmpty) yield sels.head
  val structCtors = heap.userADTCtors.slice(structCtorsOffset+structCount,
    structCtorsOffset+2*structCount)
  val structSels = heap.userADTSels.slice(structCtorsOffset+structCount,
    structCtorsOffset+2*structCount)

  val objectSorts : IndexedSeq[Sort] = objectGetters.toIndexedSeq.map(f => f.resSort)
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

  private var funRetCounter = 0
  private def getResVar (typ : CCType) : List[CCVar] = typ match {
    case CCVoid     => Nil
    case t          =>
      funRetCounter += 1
      List(new CCVar("_res" + funRetCounter, None, typ, AutoStorage)) // todo: line no?
  }

  //////////////////////////////////////////////////////////////////////////////
  private def translateProgram : Unit = {
    // First collect all declarations. This is a bit more
    // generous than actual C semantics, where declarations
    // have to be in the right order
    import IExpression._
    atomicMode = true
    val globalVarSymex = Symex(null)

    /**
     * Collect global variables and their initializers.
     */
    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Global =>
          collectVarDecls(decl.dec_, true, globalVarSymex, "", false)

        case decl : Chan =>
          for (name <- decl.chan_def_.asInstanceOf[AChan].listcident_) {
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

    val globalsSize = GlobalVars.size
    /**
     * Collect static variables and their initializers.
     * Static variables can appear only at the outermost scope of function
     * declarations.
     */
    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_) {
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
              stmts.liststm_.filter(_.isInstanceOf[DecS])
                            .map(_.asInstanceOf[DecS])
          }
          assert(name nonEmpty, "Empty function name before collecting its static variables.")
          decs.foreach(dec => collectVarDecls(dec.dec_, false, globalVarSymex, name, true))
        case None => // nothing needed
      }
    }

    assert(GlobalVars.vars.drop(globalsSize).forall(v => v.isStatic),
           "Non-static variables added while looking for static variables!")

    // prevent time variables, heap variable, and global ghost variables
    // from being initialised twice
    // TODO: This is very brittle and unintuitive - come up with a better solution.
    GlobalVars.inits ++= (globalVarSymex.getValues drop
      (if (modelHeap) 1 else 0) + (if (useTime) 2 else 0) +
      (if ((propertiesToCheck contains properties.MemValidCleanup) ||
           propertiesToCheck.contains(properties.MemValidTrack) &&
           TriCeraParameters.get.useMemCleanupForMemTrack) 1 else 0))
    // if while adding glboal variables we have changed the heap, the heap term
    // needs to be reinitialised as well. Happens with global array allocations.
    if (modelHeap) {
      val heapInd = GlobalVars.lastIndexWhere(heapVar)
      val initialisedHeapValue = globalVarSymex.getValues(heapInd)
      val initialHeapValue = IConstant(GlobalVars.vars(heapInd).term)
      if (modelHeap && initialisedHeapValue.toTerm != initialHeapValue) {
        GlobalVars.inits(heapInd) = initialisedHeapValue
      }
    }


    globalPreconditions = globalPreconditions &&& globalVarSymex.getGuard

    // todo: what about functions without definitions? replace Afunc type
    val functionAnnotations : Map[Afunc, Seq[(AnnotationInfo, SourceInfo)]] =
      prog.asInstanceOf[Progr].listexternal_declaration_.collect {
        case f : Afunc  =>
          val annots : Seq[Annotation] = f.function_def_ match {
            case f: AnnotatedFunc => f.listannotation_.toList
            case f: NewFuncInt    => f.listannotation_.toList
            case _: NewFunc       => Nil
          }
          // distribute the same source info to all annotations
          // todo: can we be more fine-grained? e.g., to pinpoint which post-condition is failing
          implicit def flattenAnnotationInfos(pair: (Seq[AnnotationInfo], SourceInfo)) :
          Iterable[(AnnotationInfo, SourceInfo)] =
            pair._1.map(info => (info, pair._2))

          (f, (for (annot <- annots) yield {
            (AnnotationParser(annot), getSourceInfo(annot))
          }).flatten)
      }.toMap

    // functions for which contracts should be generated
    // todo: generate contracts for ACSL annotated funs
    val contractFuns : Seq[Afunc] =
      functionAnnotations.filter(_._2.exists(_._1 == ContractGen)).keys.toSeq

    val funsThatMightHaveACSLContracts : Map[Afunc, Seq[(AnnotationInfo, SourceInfo)]] =
      functionAnnotations.filter(_._2.exists(_._1.isInstanceOf[MaybeACSLAnnotation]))

    for(fun <- contractFuns ++ funsThatMightHaveACSLContracts.keys) {
      val funDef = FuncDef(fun.function_def_)
      LocalVars.pushFrame
      pushArguments(fun.function_def_)
      val functionParams = LocalVars getVarsInTopFrame

      val oldVars = allFormalVars map (v =>
        new CCVar(v.name + "_old", v.srcInfo, v.typ, v.storage))
      // the pre-condition: f_pre(preOldVars)
      val prePred = newPred(funDef.name + "_pre", oldVars,
        Some(getSourceInfo(fun)))

      // the post-condition: f_post(oldVars, postGlobalVars, postResVar)
      // we first pass all current vars in context as old vars (oldVars)
      // then we pass all effected output vars (which are globals + resVar)
      val postGlobalVars = GlobalVars.vars map (v =>
        new CCVar(v.name + "_post", v.srcInfo, v.typ, v.storage))
      val postResVar = getType(fun.function_def_) match {
        case CCVoid => None
        case _ => Some(new CCVar(funDef.name + "_res",
          Some(funDef.sourceInfo), getType(fun.function_def_), AutoStorage)) // todo: clean this (and similar code) up a bit
      }
      val postVars = oldVars ++ postGlobalVars ++ postResVar
      functionPostOldArgs.put(funDef.name, oldVars)

      val prePredArgACSLNames = allFormalVars map (_.name)
      val postPredACSLArgNames =
        allFormalVars.map(v => "\\old(" + v.name + ")") ++
        GlobalVars.vars.map(v => v.name) ++
        (if(postResVar nonEmpty) Seq("\\result") else Nil)

      val postOldVarsMap: Map[String, CCVar] =
      (allFormalVars.map(_ name) zip oldVars).toMap
      val postGlobalVarsMap: Map[String, CCVar] =
        (GlobalVars.vars.map(_ name) zip postGlobalVars).toMap

      val postPred = newPred(funDef.name + "_post", postVars,
        Some(getSourceInfo(fun))) // todo: end line of fun?

      LocalVars.popFrame

      class ReaderFunctionContext extends ACSLTranslator.FunctionContext {
        def getOldVar(ident: String): Option[CCVar] =
          postOldVarsMap get ident

        def getPostGlobalVar(ident: String): Option[CCVar] =
          postGlobalVarsMap get ident

        def getParams: Seq[CCVar] = functionParams

        def getGlobals: Seq[CCVar] = GlobalVars.vars - heapVar

        def getResultVar: Option[CCVar] = postResVar

        def isHeapEnabled: Boolean = modelHeap

        def getHeap: Heap =
          if (modelHeap) heap else throw NeedsHeapModelException

        def getHeapTerm: ITerm =
          if (modelHeap) getPostGlobalVar(heapTermName).get.term
          else throw NeedsHeapModelException

        def getOldHeapTerm: ITerm =
          if (modelHeap) getOldVar(heapTermName).get.term
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
          case p: CCHeapPointer => p.typ
          case t => t
        }

        def getCtor(s: Sort): Int = sortCtorIdMap(s)

        override val getStructMap: Map[IFunction, CCStruct] = 
          structDefs.values.toSet.map((struct: CCStruct) => (struct.ctor, struct)).toMap

        override val annotationBeginSourceInfo : SourceInfo = getSourceInfo(fun)

        override val annotationNumLines : Int = // todo: this is currently incorrect - to be fixed!
          functionAnnotations(fun).head._1 match {
            case inv : MaybeACSLAnnotation => inv.annot.count(_ == '\n')+1
            case _ => 1
          }
      }

      val funContext = new FunctionContext(prePred, postPred,
        new ReaderFunctionContext, prePredArgACSLNames, postPredACSLArgNames)
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

      LocalVars.pushFrame
      val stm = pushArguments(f.function_def_)

      val prePredArgs = allFormalVarTerms.toList

      for (v <- functionPostOldArgs(name)) LocalVars addVar v

      val entryPred = newPred(Nil, Some(getSourceInfo(f)))

      val resVar = getResVar(typ)
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

      val globalVarTerms : Seq[ITerm] = GlobalVars.formalVarTerms
      val postArgs : Seq[ITerm] = (allFormalVarTerms drop prePredArgs.size) ++
        globalVarTerms ++ resVar.map(v => IConstant(v.term))

      output(addRichClause(
        postPred(postArgs) :-
          exitPred(allFormalVarTerms ++ resVar.map(v => IConstant(v.term))),
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

      LocalVars popFrame
    }

    // then translate the threads
    atomicMode = false

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
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
              LocalVars pushFrame
              val threadVar = new CCVar(thread.cident_1,
                Some(getSourceInfo(thread)), CCInt, AutoStorage)
              LocalVars addVar threadVar
              val translator = FunctionTranslator.apply(thread.cident_2)
              val finalPred = translator translateNoReturn(thread.compound_stm_)
              processes += ((clauses.toList, ParametricEncoder.Infinite))
              clauses.clear
              LocalVars popFrame
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

          LocalVars pushFrame

          val f = FuncDef(funDef)

          val returnType = {
            FuncDef(funDef).declSpecs match {
              case Some(declSpec) => getType(declSpec)
              case None => CCVoid
            }
          }

          val exitVar = getResVar(returnType)
          val exitPred = newPred(exitVar, Some(getLastSourceInfo(f.body)))

          val stm = pushArguments(funDef)

          val translator = FunctionTranslator(exitPred, f.name)

          /**
           * There can be various ways out of a function. If a function has a
           * return type, the function can still end without reaching a
           * return statement - which is why there can be multiple `finalPreds`.
           */
          val finalPreds = Seq(globalExitPred) ++ (
            if (returnType != CCVoid) {
              val exitWithoutReturnPred = translator.translateWithReturn(stm)
              Seq(exitWithoutReturnPred, exitPred)
            }
            else Seq(translator.translateNoReturn(stm)))

          /**
           * Add an assertion that all pointers that are in scope at the
           * exit of `entryFunction` are freed using the prophecy variable.
           * This ensures [[properties.MemValidCleanup]].
          */
          if (modelHeap &&
              ((propertiesToCheck contains properties.MemValidCleanup) ||
               propertiesToCheck.contains(properties.MemValidTrack) &&
               TriCeraParameters.get.useMemCleanupForMemTrack)) {
            val heapInd = GlobalVars.lastIndexWhere(heapVar)
            val cleanupVarInd = GlobalVars.lastIndexWhere(memCleanupProphecyVar)

            if (heapInd == -1 || cleanupVarInd == -1) {
              assert(false, "Could not find the heap term or the mem-cleanup" +
                            "prophecy variable term!")
            }

            import HornClauses._
            import IExpression._
            for (finalPred <- finalPreds) finalPred match {
              case CCPredicate(_, args, _)
                if args(heapInd).sort == heap.HeapSort &&
                   args(cleanupVarInd).sort == heap.AddressSort =>

                val resVar = getResVar(args.last.typ)
                assertionClauses +=
                mkRichAssertionClause(
                    (args(cleanupVarInd).term === heap.nullAddr()) :-
                     atom(finalPred,
                          allFormalVarTerms.toList ++
                          resVar.map(v => IConstant(v.term)) take finalPred.arity),
                    None, properties.MemValidCleanup)
              case _ =>
                assert(false, s"$finalPred does not contain the heap variable or" +
                              s"the memory cleanup prophecy variable!")
            }
          }

          processes += ((clauses.toList, ParametricEncoder.Singleton))
          clauses.clear

          LocalVars popFrame
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
        val typ = decl.listdeclaration_specifier_.find(_.isInstanceOf[Type]) match {
          case Some(t) => t.asInstanceOf[Type].type_specifier_
          case None => throw new
              TranslationException("Could not determine type for " + decl)
        }
        typ match {
          case structDec : Tstruct =>
            structDec.struct_or_union_spec_ match {
              case _: Unique =>
                val declarator = decl.listinit_declarator_.head match {
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
        val typ = nodecl.listdeclaration_specifier_(0) match {
          case spec: Type => spec.type_specifier_
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

  private def isUniqueStruct(listDec : ListDeclaration_specifier) : Boolean = {
    if (listDec.nonEmpty) {
      listDec.head.isInstanceOf[Type] &&
        listDec.head.asInstanceOf[Type].type_specifier_.isInstanceOf[Tstruct] &&
        listDec.head.asInstanceOf[Type].type_specifier_.asInstanceOf[Tstruct].
          struct_or_union_spec_.isInstanceOf[Unique]
    } else false
  }

  case object InitDeclaratorWrapper {
    def apply(initDecl : Init_declarator) : InitDeclaratorWrapper = {
      val srcInfo = getSourceInfo(initDecl)
      initDecl match {
        case initDecl : OnlyDecl => InitDeclaratorWrapper(
          initDecl.declarator_, None, Nil, srcInfo)
        case initDecl : HintDecl =>
          InitDeclaratorWrapper(
            initDecl.declarator_, None, initDecl.listannotation_, srcInfo)
        case initDecl : InitDecl => InitDeclaratorWrapper(
          initDecl.declarator_, Some(initDecl.initializer_), Nil, srcInfo)
        case initDecl : HintInitDecl => InitDeclaratorWrapper(
          initDecl.declarator_, Some(initDecl.initializer_), initDecl.listannotation_,
          srcInfo)
      }
    }
  }
  case class InitDeclaratorWrapper(declarator       : Declarator,
                                   maybeInitializer : Option[Initializer],
                                   hints            : Seq[Annotation],
                                   sourceInfo       : SourceInfo)

  sealed abstract class CCDeclaration
  // todo: better handling of function declarations
  case class CCFunctionDeclaration(name       : String,
                                   typ        : CCType,
                                   directDecl : Direct_declarator,
                                   srcInfo    : SourceInfo) extends CCDeclaration
  case class CCVarDeclaration(name             : String,
                              typ              : CCType,
                              maybeInitializer : Option[Initializer],
                              hints            : Seq[Annotation],
                              isArray          : Boolean,
                              isStatic         : Boolean,
                              needsHeap        : Boolean,
                              initArrayExpr    : Option[Constant_expression],
                              srcInfo          : SourceInfo) extends CCDeclaration
  case object CCNoDeclaration extends CCDeclaration
  case class CCPredDeclaration(predHints : ListPred_hint,
                               srcInfo   : SourceInfo) extends CCDeclaration

  case class CCInterpPredDeclaration(predDecl: Pred_interp) extends CCDeclaration

  /**
   * @param dec               The declaration to collect from.
   * @param isGlobal          If this is a global declaration
   */
  private[concurrency]
  def collectVarDecls(dec      : Dec,
                      isGlobal : Boolean) : Seq[CCDeclaration] = {
    dec match {
      case decl: Declarators => {
        // S D1, D2, D3, ...
        // in C, the type of a variable is the spec type that can be further
        //   modified in init declarators. Above S is the specType.
        // example: int x1, *x2, *x3[];
        // first one is an int, second one is an int*, last is an array of int*s
        val specType = getType(decl.listdeclaration_specifier_)
        val isStatic = decl.listdeclaration_specifier_.exists {
          case s : Storage =>
            s.storage_class_specifier_.isInstanceOf[LocalProgram]
          case _ => false
        }

        // each iteration is for one of the initDecls, above D1, D2, D3
        for (initDecl <- decl.listinit_declarator_) yield {
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
                (CCArray(typeWithPtrs, None, None, ExtArray(Seq(CCInt.toSort), typeWithPtrs.toSort), arrayLocation), initArrayExpr)
              }
              // todo: adjust needsHeap below if an array type does not require heap
              // for instance if we model arrays using the theory of arrays or unroll
              CCVarDeclaration(name, arrayType, initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = true, isStatic = isStatic,
                needsHeap = false, initArrayExpr = initArrayExpr,
                srcInfo = initDeclWrapper.sourceInfo)
            case _ : MathArray =>
              CCVarDeclaration(name, CCArray(typeWithPtrs, None, None,
                ExtArray(Seq(CCInt.toSort), typeWithPtrs.toSort),
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
        Seq(CCNoDeclaration)
      case predDecl: PredDeclarator =>
        Seq(CCPredDeclaration(predDecl.listpred_hint_, getSourceInfo(predDecl)))
      case interpPredDecl: InterpPredDeclarator =>
        Seq(CCInterpPredDeclaration(interpPredDecl.pred_interp_))
    }
  }

  /**
   * This is used for collecting argument names and types of interpreted
   * predicate expressions.
   */
  private def collectArgTypesAndNames(decList : ListParameter_declaration,
                                      declName : String = "") :
    Seq[(CCType, String)] = {
    for (ind <- decList.indices) yield {
      decList(ind) match {
        case t : OnlyType => {
          if (t.listdeclaration_specifier_.exists(
            spec => !spec.isInstanceOf[Type]))
            throw new TranslationException(
              "Only type specifiers are allowed inside predicate declarations.")
          val argType = getType(
            t.listdeclaration_specifier_.map(_.asInstanceOf[Type]
                                              .type_specifier_).toIterator)
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
      }
    }
  }

  /**
   * Collects variable declarations and stores them in [[GlobalVars]] and
   * [[LocalVars]] (depending on the value of `isGlobal`. It also stores
   * their initial values in the passed `values` [[Symex]].
   * @param dec               The declaration to collect from.
   * @param isGlobal          If this is a global declaration
   * @param values            This [[Symex]] will be used to fill in the
   *                          extracted values.
   * @param enclosingFuncName Current function (if not global)
   * @param colelctOnlyLocalStatic If set, signals this is collecting static
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
        if varDec.isStatic && !collectOnlyLocalStatic ||
           !varDec.isStatic && collectOnlyLocalStatic =>
      /**
       * Do nothing when
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

        val storage = varDec.isStatic match {
          case true => StaticStorage(enclosingFuncName)
          case false => if(isGlobal) GlobalStorage else AutoStorage
        }
        val lhsVar = new CCVar(varDec.name, Some(varDec.srcInfo), varDec.typ,
                               storage)
        val srcInfo = lhsVar.srcInfo

        val (actualLhsVar, initValue, initGuard) =
          varDec.maybeInitializer match {
            case Some(init : InitExpr) =>
              if (init.exp_.isInstanceOf[Enondet]) {
                (lhsVar, CCTerm(lhsVar.term, varDec.typ, srcInfo),
                  lhsVar rangePred)
              } else {
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
                      (lhsVar, CCTerm(heap.nullAddr(), varDec.typ, srcInfo))
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
              }
            case Some(_ : InitListOne) | Some(_: InitListTwo) => {
              val initStack =
                getInitsStack(varDec.maybeInitializer.get, values)
              varDec.typ match {
                case structType : CCStruct =>
                  (lhsVar, CCTerm(structType.getInitialized(initStack), varDec.typ, srcInfo),
                    lhsVar rangePred)
                case arrayPtr : CCHeapArrayPointer =>
                  val addressRangeValue = varDec.initArrayExpr match {
                    case Some(expr) =>
                      val arraySizeTerm =
                        values.eval(expr.asInstanceOf[Especial].exp_)(
                          values.EvalSettings(), values.EvalContext())
                      val arraySize = arraySizeTerm match {
                        case CCTerm(IIntLit(IdealInt(n)), actualType, srcInfo)
                          if actualType.isInstanceOf[CCArithType] => n
                        case _ => throw new TranslationException(
                          "Array with non-integer" +
                            "size specified in an intialized array expression!")
                      }
                      import IExpression._
                      val heapInd = GlobalVars.lastIndexWhere(heapVar)
                      val initHeapTerm =
                        if (values.getValues(heapInd).toTerm == IConstant(heapTerm)) {
                          CCTerm(GlobalVars.inits(heapInd).toTerm, CCHeap(heap), srcInfo)
                        } else
                          CCTerm(values.getValues(heapInd).toTerm, CCHeap(heap), srcInfo)
                      val objTerm = CCTerm(arrayPtr.elementType.getZeroInit,
                        arrayPtr.elementType, srcInfo)
                      val arrayTerm =
                        values.heapBatchAlloc(objTerm, arraySizeTerm.toTerm, initHeapTerm)
                      def getInitializedObj = {
                        if (initStack.nonEmpty) {
                          arrayPtr.elementType match {
                            case structType: CCStruct =>
                              structType.getInitialized(initStack)
                            case _ => initStack.pop // todo: union types, array types
                          }
                        }
                        else arrayPtr.elementType.getZeroInit
                      }
                      for(i <- 0 until arraySize)
                        values.heapWrite(heap.nth(arrayTerm, i),
                          getInitializedObj, arrayPtr.elementType.toSort)
                      arrayTerm
                    case None =>
                      throw new TranslationException("Cannot initialize" +
                        "arrays with unknown size")
                  }
                  // initialise using the first address of the range
                  (lhsVar, CCTerm(addressRangeValue, varDec.typ, srcInfo), IExpression.i(true))
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
                  val objValue = if (isGlobal || collectOnlyLocalStatic)
                                   typ.elementType.getZeroInit
                  else typ.elementType.getNonDet
                  val objTerm = CCTerm(objValue, typ.elementType, srcInfo)
                  val heapInd = GlobalVars.lastIndexWhere(heapVar)
                  val initHeapTerm =
                    if (values.getValues(heapInd).toTerm == IConstant(heapTerm)) {
                      CCTerm(GlobalVars.inits(heapInd).toTerm, CCHeap(heap), srcInfo)
                    } else
                      CCTerm(values.getValues(heapInd).toTerm, CCHeap(heap), srcInfo)
                  val addressRangeValue = varDec.initArrayExpr match {
                    case Some(expr) =>
                      val arraySize =
                        values.eval(expr.asInstanceOf[Especial].exp_)(
                          values.EvalSettings(), values.EvalContext())
                      values.heapBatchAlloc(objTerm, arraySize.toTerm, initHeapTerm)
                    case None =>
                      heap.addressRangeCtor(heap.nullAddr(), IIntLit(0))
                  }
                  // initialise using the first address of the range
                  (lhsVar, CCTerm(addressRangeValue, typ, srcInfo), IExpression.i(true))
                case _ if isGlobal || collectOnlyLocalStatic  =>
                  (lhsVar, CCTerm(varDec.typ.getZeroInit, varDec.typ, srcInfo),
                    lhsVar rangePred)
                case _ =>
                  (lhsVar, CCTerm(lhsVar.term, varDec.typ, srcInfo),
                    lhsVar rangePred)
              }
          }

        // do not use actualType below, take from lhsVar

        if (isGlobal || collectOnlyLocalStatic) {
          GlobalVars addVar actualLhsVar
          variableHints += List()
        } else {
          LocalVars addVar actualLhsVar
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
        for (hint <- predDec.predHints) {
          hint match {
            case predHint : PredicateHint =>
              // todo: refactor this using other code collecting parameter information
              val decList = predHint.parameter_type_.asInstanceOf[AllSpec]
                .listparameter_declaration_
              val argTypesAndNames : Seq[(CCType, String)] =
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
            val argTypesAndNames : Seq[(CCType, String)] =
              collectArgTypesAndNames(decList, predExp.cident_)

            val ccVars = argTypesAndNames.map{
              case (typ, name) =>
                new CCVar(name, Some(getSourceInfo(predExp)), typ, AutoStorage)
            }
            values.saveState
            ccVars.foreach(LocalVars addVar)
            for ((ccVar, ind) <- ccVars.zipWithIndex) {
              values.addValue(CCTerm(IExpression.v(ind), ccVar.typ, ccVar.srcInfo))
            }
            val predFormula : CCFormula =
              values.eval(predExp.exp_)(values.EvalSettings(
                noClausesForExprs = true), values.EvalContext()) match {
              case f : CCFormula => f
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

  private def processHints(hintAnnotations : Seq[Annotation]) : Unit = {
    val hints : Seq[AbsHintClause] = (for (hint <- hintAnnotations) yield {
      AnnotationParser(hint)
    }).flatten.filter(_.isInstanceOf[AbsHintClause]).
      map(_.asInstanceOf[AbsHintClause])
    if (hints.nonEmpty) {
      val hintSymex = Symex(null)
      hintSymex.saveState

            val subst =
              (for ((v, n) <-
                      (GlobalVars.iterator ++ LocalVars.iterator).zipWithIndex)
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

            variableHints(variableHints.size - 1) = hintEls
          }
    }

  private def getName (f : Function_def) : String = getName(FuncDef(f).decl)
  private def getName (t : Thread_def) : String = t match {
    case decl : SingleThread => decl.cident_
    case decl : ParaThread => decl.cident_2
  }

  private def getName(decl : Declarator) : String = decl match {
    case decl : NoPointer => getName(decl.direct_declarator_)
    case decl : BeginPointer => getName(decl.direct_declarator_)
  }

  private def getName(decl : Direct_declarator) : String = decl match {
    case decl : Name      => decl.cident_
    case decl : ParenDecl => getName(decl.declarator_)
    case dec : NewFuncDec => getName(dec.direct_declarator_)
//    case dec : OldFuncDef => getName(dec.direct_declarator_)
    case dec : OldFuncDec => getName(dec.direct_declarator_)
    case dec : InitArray => getName(dec.direct_declarator_)
    case dec : Incomplete => getName(dec.direct_declarator_)
    case dec : MathArray => getName(dec.direct_declarator_)
  }

  private def getType(specs : Seq[Declaration_specifier]) : CCType =
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
      getType(for (qual <- name.listspec_qual_.iterator;
                   if (qual.isInstanceOf[TypeSpec]))
              yield qual.asInstanceOf[TypeSpec].type_specifier_)
    case name : ExtendedType =>
      val typ = getType(for (qual <- name.listspec_qual_.iterator;
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
      (for (qual <- fields.asInstanceOf[Structen].listspec_qual_.iterator;
           if (qual.isInstanceOf[TypeSpec]))
        yield qual.asInstanceOf[TypeSpec].type_specifier_).toList
    specs.find(s => s.isInstanceOf[Tenum]) match {
      case Some(enum) => buildEnumType(enum.asInstanceOf[Tenum])
      case None =>
        val (maybeDecl, maybeConstExpr) =
          fields.asInstanceOf[Structen].liststruct_declarator_.head match {
            case f : Decl =>
              (Some(f.declarator_), None)
            case f : Field =>
              (None, f.constant_expression_)
            case f : DecField =>
              (Some(f.declarator_), Some(f.constant_expression_))
          }

        val typ = getType(specs.toIterator)
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
                ExtArray(Seq(CCInt.toSort), typ.toSort), ArrayLocation.Heap) // todo: only int indexed arrays
            case initArray: InitArray =>
              val arraySizeSymex = Symex(null)
              val evalSettings = arraySizeSymex.EvalSettings()
              val evalContext = arraySizeSymex.EvalContext()
              val arraySizeExp = arraySizeSymex.eval(
                initArray.constant_expression_.asInstanceOf[Especial].exp_)(
                evalSettings, evalContext
              )
              val arraySize = arraySizeExp match {
                case CCTerm(IIntLit(IdealInt(n)), typ, srcInfo)
                  if typ.isInstanceOf[CCArithType] => n
                case _ => throw new TranslationException("Array with non-integer" +
                  "size specified inside struct definition!")
              }
              CCArray(typ, Some(arraySizeExp), Some(arraySize),
                ExtArray(Seq(arraySizeExp.typ.toSort), typ.toSort),
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
    getAnonName(".AS")

  private def getAnonEnumName: String =
    getAnonName(".ES")

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
      case dec: Tag => dec.liststruct_dec_
      case dec: Unique =>
        uniqueStructs += ((dec, structName))
        dec.liststruct_dec_
      case _ => throw new TranslationException("struct can only be built" +
        "with Unique or Tag types!")
    }

    val fieldList : IndexedSeq[FieldInfo] = (for (field <- fields) yield {

      // ignoring all qual specs such as volatile, const etc.
      val specs : List[Type_specifier] =
        (for (f <- field.asInstanceOf[Structen].listspec_qual_
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
      val declarators = field.asInstanceOf[Structen].liststruct_declarator_

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
        buildEnumType(dec.listenumerator_, getAnonEnumName)
      case named : EnumName =>
        buildEnumType(named.listenumerator_, named.cident_)
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
        buildEnumType(dec.listenumerator_, getAnonEnumName)
      case named : EnumName =>
        buildEnumType(named.listenumerator_, named.cident_)
      case _ => CCInt
    }
  }

  private def buildEnumType (specs: Seq[Enumerator],
                             enumName: String) : CCType = {
    if (enumDefs contains enumName)
      throw new TranslationException(
        "enum " + enumName + " is already defined")

    def addEnumerator(name : String, t : CCExpr) = {
      if (enumeratorDefs contains name)
        throw new TranslationException(
          "enumerator " + name + " already defined")
      enumeratorDefs.put(name, t)
    }
    {
      // map the enumerators to integers directly
      var nextInd = IdealInt.ZERO
      var enumerators = new MHashMap[String, IdealInt]
      val symex = Symex(null) // a temporary Symex to collect enum declarations
      // to deal with fields referring to same-enum fields, e.g. enum{a, b = a+1}
      LocalVars pushFrame // we also need to add them as vars

      for (s <- specs) s match {
        case s : Plain => {
          val ind = nextInd
          nextInd = nextInd + 1
          val v = new CCVar(s.cident_, Some(getSourceInfo(s)), CCInt, AutoStorage)
          LocalVars addVar v
          symex.addValue(CCTerm(IIntLit(ind), CCInt, v.srcInfo))
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
          LocalVars addVar v
          symex.addValue(CCTerm(IIntLit(ind), CCInt, v.srcInfo))
          enumerators += ((s.cident_, ind))
        }
      }

      LocalVars popFrame

      val newEnum = CCIntEnum(enumName, enumerators.toSeq)
      enumDefs.put(enumName, newEnum)

      for ((n, v) <- enumerators)
        addEnumerator(n, CCTerm(v, newEnum, None)) // todo: srcInfo?
      newEnum
    }
  }

  /*private def updateArraySize (arrayTyp : CCArray, decl : OnlyDecl) = {
    if (arraySizes contains arrayTyp)
      throw new TranslationException(
        "size of " + arrayTyp + " is already defined")

    val symex = Symex(null) // a temporary Symex to collect the array size

    /*val arraySize = decl match {
      case initArray : InitArray => // todo: maybe this can be calculated beforehand, so we actually have an integer constant here?
        Some(symex.eval(initArray.constant_expression_.asInstanceOf[Especial].exp_)) // todo: n-d arrays?
      case _ : Incomplete => None // no size information
    }*/
    arraySizes += ((arrayTyp, arraySize))
  }*/

  private def getType(typespec : Type_specifier) : CCType = {
    getType(Seq(typespec).iterator)
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
    if(f.decl.isInstanceOf[BeginPointer]) CCHeapPointer(heap, typ) // todo: can be stack pointer too, this needs to be fixed
    else typ
  }

  private def translateClockValue(expr : CCExpr) : CCExpr = {
    import IExpression._
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm(GT.term + GTU.term*(-v), CCClock, expr.srcInfo)
      case t if (expr.typ == CCClock) =>
        CCTerm(t, CCClock, expr.srcInfo)
      case t if (expr.typ == CCDuration) =>
        CCTerm(GT.term - t, CCClock, expr.srcInfo)
      case t =>
        throw new TranslationException(
          "clocks can only be set to or compared with integers")
    }
  }

  private def translateDurationValue(expr : CCExpr) : CCExpr = {
    import IExpression._
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case _ if (expr.typ == CCDuration) =>
        expr
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm(GTU.term*v, CCDuration, expr.srcInfo)
      case t =>
        throw new TranslationException(
          "duration variable cannot be set or compared to " + t)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateConstantExpr(expr : Constant_expression,
                                    symex : Symex = Symex(null)) : CCExpr = {
    symex.saveState
    val res = symex.eval(expr.asInstanceOf[Especial].exp_)(
      symex.EvalSettings(), symex.EvalContext())
    if (!symex.atomValuesUnchanged)
      throw new TranslationException(
        "constant expression is not side-effect free")
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Symex {
    def apply(initPred : CCPredicate) = {
      val values = new ArrayBuffer[CCExpr]
      values ++= allFormalExprs
      new Symex(initPred, values)
    }
  }

  private def atom(ccPred : CCPredicate, args : Seq[ITerm]) : IAtom = {
    if (ccPred.arity != args.size) {
      throw new TranslationException(getLineString(ccPred.srcInfo) +
        s"$ccPred expects ${ccPred.arity} argument(s)" +
        s", but got ${args.size}: " + args.mkString(", "))
    }
    IAtom(ccPred.pred, args)
  }
  private def atom(ccPred : CCPredicate) : IAtom =
    atom(ccPred, ccPred.argVars.map(_.term))

  private class Symex private (oriInitPred : CCPredicate,
                               values : Buffer[CCExpr]) {
    private var guard : IFormula = true

    def addGuard(f : IFormula) : Unit = {
      guard = guard &&& f
      touchedGlobalState =
        touchedGlobalState || !freeFromGlobal(f)
    }

    def getGuard = guard

    //todo:Heap get rid of this or change name
    def heapRead(ptrExpr : CCExpr, assertMemSafety : Boolean = true,
                 assumeMemSafety : Boolean = true)
    : CCTerm = {
      val (objectGetter, typ : CCType) = ptrExpr.typ match {
        case typ : CCHeapPointer => (sortGetterMap(typ.typ.toSort), typ.typ)
        case _ => throw new TranslationException(
          "Can only read from heap pointers! (" + ptrExpr + ")")
      }
      val readObj = heap.read(getValue(heapTermName, "").toTerm, ptrExpr.toTerm)
      if (assertMemSafety && propertiesToCheck.contains(properties.MemValidDeref)) {
        assertProperty(
          heap.heapADTs.hasCtor(readObj, sortCtorIdMap(typ.toSort)),
          ptrExpr.srcInfo, properties.MemValidDeref)
        // todo: add tester methods for user ADT sorts?
        // also add memory safety assumptions to the clause
        if (assumeMemSafety)
          addGuard(heap.heapADTs.hasCtor(readObj, sortCtorIdMap(typ.toSort)))
      }
      CCTerm(objectGetter(readObj), typ, ptrExpr.srcInfo)
    }
    def heapAlloc(value : CCTerm) : CCTerm = {
      val objTerm = sortWrapperMap(value.typ.toSort)(value.toTerm)
      val newAlloc = heap.alloc(getValue(heapTermName, "").toTerm, objTerm)
      setValue(heapTerm.name, CCTerm(
        heap.newHeap(newAlloc), CCHeap(heap), value.srcInfo), "")
      CCTerm(heap.newAddr(newAlloc), CCHeapPointer(heap, value.typ), value.srcInfo)
    }
    // batch allocates "size" "objectTerm"s, returns the address range
    // if "initHeapTerm" is passed, that is used as the initial heap term
    def heapBatchAlloc(value : CCTerm, size : ITerm,
                       initHeapTerm : CCExpr = getValue(heapTermName, "")) : ITerm = {
      val newBatchAlloc =
        heap.batchAlloc(initHeapTerm.toTerm,
                        sortWrapperMap(value.typ.toSort)(value.toTerm), size)
      //val newAllocHeap = heap.batchAllocHeap(initHeapTerm.toTerm, objectTerm, size)
      //setValue(heapTerm.name, CCTerm(newAllocHeap, CCHeap(heap)))
      val newHeap = heap.newBatchHeap(newBatchAlloc)
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), value.srcInfo), "")
      //heap.batchAllocAddrRange(initHeapTerm.toTerm, objectTerm, size)
      heap.newAddrRange(newBatchAlloc)
    }
    def heapArrayRead(arrExpr  : CCExpr,
                      index    : CCExpr,
                      arrType  : CCHeapArrayPointer,
                      assertMemSafety : Boolean = true,
                      assumeMemSafety : Boolean = true,
                      assertIndexWithinBounds : Boolean = true) : CCTerm = {
      import IExpression._
      val readAddress = CCTerm(heap.nth(arrExpr.toTerm, index.toTerm),
        CCHeapPointer(heap, arrType.elementType), arrExpr.srcInfo)
      val readValue = heapRead(readAddress, assertMemSafety, assumeMemSafety)
      if (assertIndexWithinBounds &&
          propertiesToCheck.contains(properties.MemValidDeref))
        assertProperty(heap.within(arrExpr.toTerm, readAddress.toTerm),
                       arrExpr.srcInfo, properties.MemValidDeref)
      readValue
    }

    /**
     * updates an Object on the heap, which can also be an ADT
     * @param lhs this must be a read from the location to be updated.
     *            e.g. getInt(read(h,a)) or an ADT selector x(getS(read(h,a)))
     * @param rhs the term to be written to the location pointed by lhs
     * @param assertMemSafety add memory safety assertion
     * @param assumeMemSafety assume memory safety after write
     */
    def heapWrite(lhs : IFunApp, rhs : CCExpr,
                  assertMemSafety : Boolean = false,
                  assumeMemSafety : Boolean = false) = {
      val newHeap = heap.writeADT(lhs, rhs.toTerm).asInstanceOf[IFunApp]
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), rhs.srcInfo), "")
      if (assertMemSafety &&
          propertiesToCheck.contains(properties.MemValidDeref)) {
        def getObjAndSort(f : IFunApp) : (IFunApp, Sort) = {
          if (objectGetters contains f.fun) {
            val sort = f.fun.asInstanceOf[MonoSortedIFunction].resSort
            val obj = f.args.head.asInstanceOf[IFunApp]
            (obj, sort)
          } else if (f.args.size == 1 && f.args.head.isInstanceOf[IFunApp]) {
            getObjAndSort(f.args.head.asInstanceOf[IFunApp])
          } else
            throw new TranslationException("Cannot determine read" +
              "object from passed term")
        }
        val (writtenObj, sort) = getObjAndSort(lhs)

        assertProperty(heap.heapADTs.hasCtor(writtenObj, sortCtorIdMap(sort)),
          rhs.srcInfo, properties.MemValidDeref)
        // todo: add tester methods for user ADT sorts?
        // also add memory safety assumptions to the clause
        if (assumeMemSafety)
          addGuard(heap.heapADTs.hasCtor(writtenObj, sortCtorIdMap(sort)))
      }
    }

    /**
     * Write the passed object to the passed location on the heap
     */
      // todo: add mem-/type-safety assertions?
    def heapWrite(addr : ITerm, obj : ITerm, objSort : Sort) = {
      val heapVal = getValue(heapTerm.name, "")
      val newHeap = heap.write(heapVal.toTerm, addr, sortWrapperMap(objSort)(obj))
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), None), "") // todo: src info?
    }

    def heapBatchWrite(h : ITerm, r : ITerm, o : ITerm) = {
      val newHeap = heap.batchWrite(h, r, o)
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), None), "") // todo: src info?
    }

    /**
     * `free` is encoded by writing [[defObj]] to the pointed location.
     */
    def heapFree(t : CCExpr, srcInfo : Option[SourceInfo]) = {
      t.typ match {
        case p : CCHeapPointer =>
          val termToFree : IFunApp =
            heapRead(t, assertMemSafety = false).toTerm match {
              case IFunApp(f, Seq(arg))  if (objectGetters contains f) &
                arg.isInstanceOf[IFunApp] =>
                arg.asInstanceOf[IFunApp]
              case _ => throw new TranslationException("Could not resolve" +
                " the term to free: " + t)
            }
          if(propertiesToCheck contains properties.MemValidFree){
            /**
             * Add an assertion that `ptrExpr` is safe to free.
             * Checking [[Heap.isAlloc]] is not sufficient: freed locations are
             * marked by writing the default object to them, so we need to check
             * that read(h, p) =/= defObj. A free is also valid when
             * p is nullAddr.
             */
            val readObj = heap.read(
              getValue(heapTermName, "").toTerm, t.toTerm)
            assertProperty(t.toTerm === heap.nullAddr() |||
                           readObj =/= heap._defObj,
                           srcInfo, properties.MemValidFree)
          }
          if ((propertiesToCheck contains properties.MemValidCleanup) ||
              propertiesToCheck.contains(properties.MemValidTrack) &&
              TriCeraParameters.get.useMemCleanupForMemTrack) {
            /**
             * Set [[memCleanupProphecyVar]] back to NULL, if the freed address
             * is the same as the one stored.
             */
            val prophInd = GlobalVars.lastIndexWhere(memCleanupProphecyVar)
            val prophOldVal = getValues(prophInd).toTerm
            setValue(prophInd, CCTerm(
              IExpression.ite(prophOldVal === t.toTerm,
                              heap.nullAddr(),
                              prophOldVal), memCleanupProphecyVar.typ, None),
                     false)
          }
          heapWrite(termToFree, CCTerm(p.heap._defObj, p, srcInfo))
        case p : CCHeapArrayPointer =>
          import IExpression._
          //val n = getFreshEvalVar(CCUInt)
          //addGuard(n.term >= 0 & n.term < heap.addrRangeSize(t.toTerm))
          //val a = getFreshEvalVar(CCHeapPointer(heap, p.elementType))
          //addGuard(heap.within(t.toTerm, a.term))
          /*val termToFree : IFunApp =
            heapRead(CCTerm(a.term, a.typ),
                     assertMemSafety = false).toTerm match {
              case IFunApp(f, Seq(arg)) if (objectGetters contains f) &
                                            arg.isInstanceOf[IFunApp] =>
                arg.asInstanceOf[IFunApp]
              case _ => throw new TranslationException("Could not resolve" +
                " the term to free: " + t)
            }
          heapWrite(termToFree, CCTerm(p.heap._defObj, p))*/
          // todo: what about ADTs?
          if (propertiesToCheck contains properties.MemValidFree) {
            p.arrayLocation match {
              case ArrayLocation.Heap =>
                /**
                 * Assert that either `t` is `null`, or
                 * forall ind. t[ind] =/= defObj
                 * (or equivalently forall ind. read(h, nth(t, ind)) =/= defObj)
                 */
                val ind      = getFreshEvalVar(CCInt, t.srcInfo)
                val readAddr = heap.nth(t.toTerm, ind.term)
                val readObj  = heap.read(getValue(heapTermName, "").toTerm,
                                         readAddr)
                assertProperty(t.toTerm === heap.nullAddr() |||
                               (heap.within(t.toTerm, readAddr) ==>
                                (readObj =/= heap._defObj)),
                               srcInfo, properties.MemValidFree)
              case _ =>
                /**
                 * Freeing non-heap memory is undefined behaviour.
                 */
                assertProperty(IExpression.i(false),
                               srcInfo, properties.MemValidFree)
            }
          }
          if ((propertiesToCheck contains properties.MemValidCleanup) ||
              propertiesToCheck.contains(properties.MemValidTrack) &&
              TriCeraParameters.get.useMemCleanupForMemTrack) {
            /**
             * Set [[memCleanupProphecyVar]] back to NULL, if the beginning of
             * the freed address block is the same as the one stored.
             */
            val prophInd    = GlobalVars.lastIndexWhere(memCleanupProphecyVar)
            val prophOldVal = getValues(prophInd).toTerm
            setValue(prophInd, CCTerm(
              IExpression.ite(prophOldVal === heap.nth(t.toTerm, 0),
                              heap.nullAddr(),
                              prophOldVal), memCleanupProphecyVar.typ, None),
                     false)
          }
          heapBatchWrite(getValue(heapTermName, "").toTerm, t.toTerm, defObj())
        case _ =>
          /**
           * Freeing a non-heap pointer.
           */
          if (propertiesToCheck contains properties.MemValidFree)
            assertProperty(IExpression.i(false),
                           srcInfo, properties.MemValidFree)
      }
    }

    private var initAtom =
      if (oriInitPred == null)
        null
      else
        atom(oriInitPred, allFormalVarTerms take oriInitPred.arity)
    private def initPred = predCCPredMap(initAtom.pred)

    def initAtomArgs = if(initAtom != null) Some(initAtom.args) else None

    private val savedStates = new Stack[(IAtom, Seq[CCExpr], IFormula, /*IFormula,*/ Boolean)]
    def saveState =
      savedStates push ((initAtom, values.toList, guard, touchedGlobalState))
    def restoreState = {
      val (oldAtom, oldValues, oldGuard, /*oldPullGuard,*/ oldTouched) = savedStates.pop
      initAtom = oldAtom
      values.clear
      oldValues copyToBuffer values
      LocalVars.pop(LocalVars.size - values.size + GlobalVars.size)
      guard = oldGuard
      touchedGlobalState = oldTouched
    }

    def atomValuesUnchanged = {
      val (oldAtom, oldValues, _, /*_,*/ _) = savedStates.top
      initAtom == oldAtom &&
      ((values.iterator zip oldValues.iterator) forall {
         case (x, y) => x == y
       })
    }

    private var touchedGlobalState : Boolean = false
    private var assignedToStruct : Boolean = false

    private def maybeOutputClause(srcInfo : Option[SourceInfo]) : Unit =
      if (((!atomicMode && touchedGlobalState) || assignedToStruct))
        outputClause(srcInfo)

    private def pushVal(v : CCExpr, varName : String = "") = {
      val freshVar = getFreshEvalVar(v.typ, v.srcInfo, varName)
      addValue(v)
      // reserve a local variable, in case we need one later
      LocalVars addVar freshVar

      if (usingInitialPredicates) {
        // if the pushed value refers to other variables,
        // add initial predicates that relate the values of
        // temporary variables with the original variables
        //
        // TODO: this is currently not very effective ...

        val varMapping =
          (for (d <- v.occurringConstants.iterator;
                index = lookupVarNoException(d.name, "")) // TODO: can probably specify enclosing function?
           yield (d -> index)).toMap

        if (varMapping forall { case (_, ind) => ind >= 0 }) {
          val defTerm =
            ConstantSubstVisitor(v.toTerm,
                                 varMapping mapValues (IExpression.v(_)))
          val rhs = IExpression.v(variableHints.size - 1)

          if (defTerm != rhs) {
            val defEq = defTerm === rhs
            variableHints(variableHints.size - 1) =
              List(VerifHintInitPred(defEq))
          }
        }
      }
    }

    private def pushFormalVal(typ : CCType, srcInfo : Option[SourceInfo]) = {
      val freshVar = getFreshEvalVar(typ, srcInfo)
      LocalVars addVar freshVar
      addValue(CCTerm(freshVar.term, typ, srcInfo))
      addGuard(freshVar rangePred)
    }

    private def popVal = {
      val res = values.last
      values trimEnd 1
      LocalVars.pop(1)
      res
    }
    private def topVal = values.last
    private def removeVal(ind : Int) {
      values.remove(ind)
      LocalVars.remove(ind - GlobalVars.size)
    }

    private def outputClause(srcInfo : Option[SourceInfo]) : Unit =
      outputClause(newPred(Nil, srcInfo), srcInfo)

    def genClause(pred : CCPredicate,
                  srcInfo : Option[SourceInfo]) : CCClause = {
      import HornClauses._
      if (initAtom == null)
        throw new TranslationException("too complicated initialiser")
      val clause = asAtom(pred) :- (initAtom &&& guard)
      addRichClause(clause, srcInfo)
    }

    def outputClause(pred : CCPredicate,
                     srcInfo : Option[SourceInfo],
                     sync : ParametricEncoder.Synchronisation =
                       ParametricEncoder.NoSync) : Unit = {
      val c = genClause(pred, srcInfo)
      if (!c.clause.hasUnsatConstraint)
        output(c, sync)
      resetFields(pred)
    }

    def outputClause(headAtom : IAtom,
                     srcInfo : Option[SourceInfo]) : Unit = {
      import HornClauses._
      val clause = headAtom :- (initAtom &&& guard)
      if (!clause.hasUnsatConstraint)
        output(addRichClause(clause, srcInfo))
    }

    def resetFields(pred : CCPredicate) : Unit = {
      initAtom = atom(pred, allFormalVarTerms take pred.arity)
      guard = true
      touchedGlobalState = false
      assignedToStruct = false
      for ((e, i) <- allFormalExprs.iterator.zipWithIndex)
        values(i) = e
    }

    def outputITEClauses(cond : IFormula,
                         thenPred : CCPredicate,
                         elsePred : CCPredicate,
                         srcInfo : Option[SourceInfo]) = {
      saveState
      addGuard(cond)
      outputClause(thenPred, srcInfo)
      restoreState
      addGuard(~cond)
      outputClause(elsePred, srcInfo)
    }

    def assertProperty(property     : IFormula,
                       srcInfo      : Option[SourceInfo],
                       propertyType : properties.Property) : Unit = {
      import HornClauses._
      val clause = (property :- (initAtom &&& guard))
      assertionClauses += mkRichAssertionClause(clause, srcInfo, propertyType)
    }

    def addValue(t : CCExpr) = {
      values += t
      touchedGlobalState = touchedGlobalState || !freeFromGlobal(t)
    }

    private def getValue(name : String,
                         enclosingFunction : String,
                         isIndirection : Boolean = false) : CCExpr =
      getValue(lookupVar(name, enclosingFunction), isIndirection)
    private def getValue(ind : Int,
                         isIndirection : Boolean) : CCExpr =
      if (isIndirection)
        getPointedTerm(getPointerType(ind))
      else
        values(ind)

    private def getPointedTerm (ptrType : CCStackPointer) : CCTerm =
      ptrType.fieldAddress match {
        case Nil =>
          getValue(ptrType.targetInd, false).asInstanceOf[CCTerm]
        case _ =>
          val structVal = getValue(ptrType.targetInd, false)
          val structType = structVal.typ.asInstanceOf[CCStruct]
          CCTerm(
            structType.getFieldTerm(structVal.toTerm, ptrType.fieldAddress),
            structType.getFieldType(ptrType.fieldAddress), None) // todo: src Info?
      }

    private def setValue(name : String, t : CCExpr, enclosingFunction : String,
                         isIndirection : Boolean = false) : Unit =
      setValue(lookupVar(name, enclosingFunction), t, isIndirection)
    private def setValue(ind: Int, t : CCExpr,
                         isIndirection : Boolean) : Unit = {
      val actualInd = getValue(ind, false).typ match {
        case stackPtr: CCStackPointer => stackPtr.targetInd
        case _ => ind
      }
      values(actualInd) = t
      /* if(isIndirection) {
        //val ptrType = getPointerType(ind)
        getValue(ind, false).typ match {
          case stackPtr : CCStackPointer =>
            val actualInd = getActualInd(ind)
            values(actualInd) = t/* stackPtr.fieldAddress match {
              case Nil => t
              case _ =>
                val pointedStruct = values(stackPtr.targetInd)
                val structType = pointedStruct.typ.asInstanceOf[CCStruct]
                CCTerm(
                  structType.setFieldTerm(
                    pointedStruct.toTerm, t.toTerm, stackPtr.fieldAddress),
                  structType)
            }*/
            actualInd
          case _ => throw new TranslationException(
            "Trying to use a non-pointer as a pointer!")
        }
      }
      else {
        values(ind) = t
        ind
      }*/
      touchedGlobalState =
        touchedGlobalState || actualInd < GlobalVars.size || !freeFromGlobal(t)
    }

    private def getVar (ind : Int) : CCVar = {
      if (ind < GlobalVars.size) GlobalVars.vars(ind)
      else LocalVars.vars(ind - GlobalVars.size)
    }
    private def getVar (name : String, enclosingFunction : String) : CCVar = {
      val ind = lookupVar(name, enclosingFunction)
      getVar(ind)
    }

    def getValues : Seq[CCExpr] =
      values.toList
    def getValuesAsTerms : Seq[ITerm] =
      for (expr <- values.toList) yield expr.toTerm

    def asAtom(pred : CCPredicate) = atom(pred, getValuesAsTerms.take(pred.arity))

    def asLValue(exp : Exp) : String = exp match {
      case exp : Evar    => exp.cident_
      case exp : Eselect => asLValue(exp.exp_)
      case exp : Epoint  => asLValue(exp.exp_)
      case exp : Epreop  => asLValue(exp.exp_)
      case exp : Eassign => asLValue(exp.exp_1)
      case exp : Earray  => asLValue(exp.exp_1)
      case exp =>
        throw new TranslationException(
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isClockVariable(exp : Exp, enclosingFunction : String)
    : Boolean = exp match {
      case exp : Evar => getValue(exp.cident_,
                                  enclosingFunction).typ == CCClock
      case _ : Eselect | _ : Epreop | _ : Epoint | _ : Earray => false
      case exp =>
        throw new TranslationException(getLineString(exp) +
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isDurationVariable(exp : Exp, enclosingFunction : String)
    : Boolean = exp match {
      case exp : Evar => getValue(exp.cident_,
                                  enclosingFunction).typ == CCDuration
      case _ : Eselect | _ : Epreop | _ : Epoint | _ : Earray => false
      case exp =>
        throw new TranslationException(getLineString(exp) +
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isHeapRead(t : CCExpr) =
      t.toTerm match {
        case IFunApp(f, _) if objectGetters contains f => true
        case _ => false
      }
      /*t.toTerm.isInstanceOf[IFunApp] &&
        t.toTerm.asInstanceOf[IFunApp] match {
          case Left(c) => c.sort.isInstanceOf[Heap.HeapSort]
          case Right(f) => objectGetters contains f.fun
        }*/
    private def isHeapStructFieldRead (t : CCExpr) =
      t.toTerm match {
        case f : IFunApp => getFieldInfo(f)._2.isRight
        case _ => false
      }

    private def isHeapPointer(t : CCExpr) =
      t.typ match {
        case _ : CCHeapPointer      => true
        case _ : CCHeapArrayPointer => true
        case _                      => false
      }
    private def isHeapPointer(exp : Exp, enclosingFunction : String) =
      getVar(asLValue(exp), enclosingFunction).typ match {
        case _ : CCHeapPointer      => true
        case _ : CCHeapArrayPointer => true
        case _                      => false
      }

    private def isIndirection(exp : Exp) : Boolean =
      exp match {
        case exp : Epreop => exp.unary_operator_.isInstanceOf[Indirection]
        case _ => false
      }

    private def getPointerType(ind : Int) = {
      getValue(ind, false).typ match {
        case ptrType : CCStackPointer => ptrType
        case _ => throw new TranslationException(
          "Trying to use non-pointer as a pointer!")
      }
    }

    def eval(exp : Exp)(implicit evalSettings : EvalSettings,
                                 evalCtx      : EvalContext) : CCExpr = {
      val initSize = values.size
      evalHelp(exp)(evalSettings, evalCtx)
      val res = popVal
      assert(initSize == values.size)
      res
    }

    def evalList(exp : Exp) : Seq[CCExpr] = {
      val res = new ArrayBuffer[CCExpr]

      var e = exp
      while (e.isInstanceOf[Ecomma]) {
        val ec = e.asInstanceOf[Ecomma]
        res += eval(ec.exp_2)(EvalSettings(), EvalContext())
        e = ec.exp_1
      }

      res += eval(e)(EvalSettings(), EvalContext())

      res.toList
    }

    def atomicEval(exp : Exp, evalCtx : EvalContext) : CCExpr =
      atomicEval(List(exp), evalCtx, Some(getSourceInfo(exp)))

    def atomicEval(exps : Seq[Exp], evalCtx : EvalContext,
                   srcInfo : Option[SourceInfo]) : CCExpr = {
      val currentClauseNum = clauses.size
      val initSize = values.size

      inAtomicMode {
        pushVal(CCFormula(true, CCVoid, None))
        for (exp <- exps) {
          popVal
          evalHelp(exp)(EvalSettings(), evalCtx) // todo: EvalSettings(true)?
        }
      }

      if (currentClauseNum != clauses.size) {
        outputClause(srcInfo)
        mergeClauses(currentClauseNum)
      }
      val res = popVal
      assert(initSize == values.size)
      res
    }

    def atomicEvalFormula(exp : Exp, evalCtx : EvalContext) : CCFormula = {
      val initSize         = values.size

      inAtomicMode{
        evalHelp(exp)(EvalSettings(), evalCtx)
      }

      val res = popVal
      assert(initSize == values.size)
      CCFormula(res.toFormula, res.typ, res.srcInfo)
    }

    // This function returns the actual term after an assignment is done.
    // E.g. for non ADT lhs, this is the same as the rhs,
    //      for ADT lhs, this is the lhs updated with the value of rhs.
    private def getActualAssignedTerm(lhs: CCExpr, rhs: CCExpr) = {
      if (rhs.typ.isInstanceOf[CCStruct] && (rhs.typ != lhs.typ))
        throw new TranslationException("Cannot assign " + rhs.typ +
          " to " + lhs.typ + "!")

        lhs.toTerm match {
        case fieldFun : IFunApp => // an ADT
          assignedToStruct = true
          val (fieldSelectors, rootTerm) = getFieldInfo(fieldFun)

          rootTerm match {
            case Left(t) =>
              val structType = structDefs(t.sort.name)
              val fieldAddress = structType.getFieldAddress(fieldSelectors)
              CCTerm(structType.setFieldTerm(t, rhs.toTerm, fieldAddress),
                structType, rhs.srcInfo)
            case Right(f) =>
              val structType =
                structDefs(f.fun.asInstanceOf[MonoSortedIFunction].resSort.name)
              val fieldAddress = structType.getFieldAddress(fieldSelectors)
              CCTerm(structType.setFieldTerm(f, rhs.toTerm, fieldAddress),
                structType, rhs.srcInfo)
            /*case _ => {getVarType(rootTerm.name) match {
                case ptr : CCStackPointer => getPointedTerm(ptr).typ
                case typ => typ
              }}.asInstanceOf[CCStruct]*/
          }
        case _ => rhs // a non ADT
      }
    }

    // Returns the root term and a list of selectors pointing to the given field.
    // todo: this works incorrectly when root is not a pointer but the field is
    // e.g. getInt(read(h, f(someStruct)))
    private def getFieldInfo(nested : IFunApp) :
    (List[IFunction], Either[SortedConstantTerm, IFunApp]) = {
      val fieldSelectors = List()
      getFieldInfo(nested, fieldSelectors)
    }
    private def getFieldInfo(nested : IFunApp, fieldSelectors : List[IFunction])
    : (List[IFunction], Either[SortedConstantTerm, IFunApp]) = {
      nested.args.size match {
        case n if n > 1 => (fieldSelectors, Left(getStructTerm(nested)))
        case n if n == 1 =>
          nested.args.head match{
            case nestedMore : IFunApp if !(objectGetters contains nestedMore.fun) =>
              getFieldInfo(nestedMore, nested.fun :: fieldSelectors)
            case objectGetter : IFunApp =>
              (nested.fun :: fieldSelectors, Right(objectGetter))
            case lastLevel : IConstant =>
              (nested.fun :: fieldSelectors,
                Left(lastLevel.c.asInstanceOf[SortedConstantTerm]))
          }
        case _ => throw new TranslationException("Cannot get field selectors " +
          "from given struct term " + nested)
      }
    }
    private def getStructTerm(nested : ITerm) : SortedConstantTerm = { // todo
      nested match {
        case nestedMore : IFunApp => getStructTerm(nestedMore.args.head)
        case lastLevel : IConstant => lastLevel.c.asInstanceOf[SortedConstantTerm]
        case _ => throw new TranslationException(nested + " is not a struct.")
      }
    }

    case class EvalSettings(noClausesForExprs : Boolean = false)
    case class EvalContext(
        evaluatingLHS           : Boolean = false,
        handlingFunContractArgs : Boolean = false,
        lhsIsArrayPointer       : Boolean = false,
        enclosingFunctionName   : String = "",
        nestedCallDepth         : Int = 0) {
      def withLhsIsArrayPointer(set : Boolean) : EvalContext =
        copy(lhsIsArrayPointer = set)
      def withEvaluatingLHS(set : Boolean) : EvalContext =
        copy(evaluatingLHS = set)
      def withHandlingFunContractArgs(set : Boolean) : EvalContext =
        copy(handlingFunContractArgs = set)
      def withFunctionName(name : String) : EvalContext =
        copy(enclosingFunctionName = name)
      def incrementCallDepth : EvalContext =
        copy(nestedCallDepth = nestedCallDepth + 1)
    }

    private def evalHelp(exp : Exp)
                        (implicit evalSettings : EvalSettings,
                                  evalCtx      : EvalContext)
    : Unit = exp match {
      case exp : Ecomma =>
        evalHelp(exp.exp_1)
        popVal
        maybeOutputClause(Some(getSourceInfo(exp)))
        evalHelp(exp.exp_2)
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign] &&
                             isClockVariable(exp.exp_1,
                                             evalCtx.enclosingFunctionName)) =>
        evalHelp(exp.exp_2)
        maybeOutputClause(Some(getSourceInfo(exp)))
        setValue(asLValue(exp.exp_1), translateClockValue(topVal),
                 evalCtx.enclosingFunctionName)
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign] &&
                             isDurationVariable(exp.exp_1,
                                                evalCtx.enclosingFunctionName)) =>
        evalHelp(exp.exp_2)
        maybeOutputClause(Some(getSourceInfo(exp)))
        setValue(asLValue(exp.exp_1), translateDurationValue(topVal),
                 evalCtx.enclosingFunctionName)
      case exp : Eassign if exp.assignment_op_.isInstanceOf[Assign] =>
        // if lhs is array pointer, an alloc rhs evaluation should produce an
        // AddressRange even if the allocation size is only 1.
        evalHelp(exp.exp_2) //first evaluate rhs and push
        maybeOutputClause(Some(getSourceInfo(exp)))
        val rhsVal = popVal
        val lhsVal = eval(exp.exp_1) //then evaluate lhs and get it
        val updatingPointedValue =
          isHeapRead(lhsVal) || // *(p) = ... where p is a heap ptr
          isHeapStructFieldRead(lhsVal) // ps->f = ... where ps is a heap ptr
        val lhsIsArraySelect =
          lhsVal.toTerm match {
            case IFunApp(ExtArray.Select(_), _) => true
            case _ => false
          }
        if(evalCtx.lhsIsArrayPointer || isHeapPointer(lhsVal) || updatingPointedValue ||
          lhsIsArraySelect) {
          if (updatingPointedValue)
            heapWrite(lhsVal.toTerm.asInstanceOf[IFunApp], rhsVal, true, true)
          else if (lhsIsArraySelect) { // todo: this branch needs to be rewritten, it was hastily coded to deal with arrays inside structs.
            val newTerm = CCTerm(
              writeADT(lhsVal.toTerm.asInstanceOf[IFunApp],
                         rhsVal.toTerm, heap.userADTCtors, heap.userADTSels),
                       lhsVal.typ, rhsVal.srcInfo)
            val lhsName = asLValue(exp.exp_1)
            val oldLhsVal = getValue(lhsName, evalCtx.enclosingFunctionName)
            val innerTerm = lhsVal.toTerm.asInstanceOf[IFunApp].args.head
            val actualLhsTerm = getActualAssignedTerm(
              CCTerm(innerTerm, oldLhsVal.typ, rhsVal.srcInfo), newTerm)
            setValue(asLValue(exp.exp_1), actualLhsTerm,
                     evalCtx.enclosingFunctionName)
          } else {
            val lhsName = asLValue(exp.exp_1)
            val actualRhsVal = rhsVal match {
              case CCTerm(_, stackPtr@CCStackPointer(_,_,_), srcInfo) =>
                throw new UnsupportedCFragmentException(
                  getLineStringShort(srcInfo) +
                  " Only limited support for stack pointers")
              case CCTerm(IIntLit(value), _, _) =>
                if (value.intValue != 0) {
                  throw new TranslationException("Pointer arithmetic is not " +
                    "allowed, and the only assignable integer value for " +
                    "pointers is 0 (NULL)")
                } else CCTerm(heap.nullAddr(), CCHeapPointer(heap, lhsVal.typ), rhsVal.srcInfo)
              case _ => rhsVal
            }
            val actualLhsTerm = getActualAssignedTerm(lhsVal, actualRhsVal)
            rhsVal.typ match {
              case arrayPtr1 : CCHeapArrayPointer =>
                lhsVal.typ match {
                  case _ : CCHeapPointer =>
                    throw new TranslationException(getLineString(exp) +
                      "Cannot assign an array value to " + lhsName + ". " +
                      "Declaring " + lhsName + " as " + lhsName + "[] might " +
                      "solve this issue.")
                  case arrayPtr2 : CCHeapArrayPointer =>
                    if (arrayPtr1 != arrayPtr2) {
                      if (arrayPtr1.arrayLocation == ArrayLocation.Stack &&
                          arrayPtr2.arrayLocation == ArrayLocation.Heap) // -> alloca
                        updateVarType(lhsName, arrayPtr1,
                                      evalCtx.enclosingFunctionName) // todo: replace with a static analysis? we should detect arrays on stack beforehand maybe?
                      else throw new UnsupportedCFragmentException(getLineString(exp) +
                        "Pointer " + lhsName +
                        " points to elements of multiple arrays (or array types)." +
                        "Try initialising the array directly.")
                    }
                  case _ => // nothing
                }
              case _ => // nothing
            }
            setValue(lhsName, actualLhsTerm, evalCtx.enclosingFunctionName)
          }
        } else {
          val lhsName = asLValue(exp.exp_1)
          val actualLhsTerm = getActualAssignedTerm(lhsVal, rhsVal)
          setValue(lhsName, actualLhsTerm, evalCtx.enclosingFunctionName)
        }
        pushVal(rhsVal)
      case exp : Eassign =>
        evalHelp(exp.exp_1)
        val lhsVal = topVal
        maybeOutputClause(Some(getSourceInfo(exp)))
        evalHelp(exp.exp_2)
        maybeOutputClause(Some(getSourceInfo(exp)))
        val rhsE = popVal
        val rhs = rhsE.toTerm
        val lhsE = popVal
        val lhs = lhsE.toTerm
        if (lhsE.typ == CCClock || lhsE.typ == CCDuration)
          throw new TranslationException("unsupported assignment to clock")
        val newVal = CCTerm(lhsE.typ cast (exp.assignment_op_ match {
          case _ : AssignMul =>
            ap.theories.nia.GroebnerMultiplication.mult(lhs, rhs)
          case _ : AssignDiv =>
            ap.theories.nia.GroebnerMultiplication.tDiv(lhs, rhs)
          case _ : AssignMod =>
            ap.theories.nia.GroebnerMultiplication.tMod(lhs, rhs)
          case _ : AssignAdd =>
            (lhsE.typ, rhsE.typ) match {
              case (arrTyp : CCHeapArrayPointer, _ : CCArithType) =>
                import arrTyp.heap._
                addressRangeCtor(nth(lhs, rhs), addrRangeSize(lhs) - rhs)
              case _ => lhs + rhs
            }
          case _ : AssignSub =>
            (lhsE.typ, rhsE.typ) match {
              case (arrType : CCHeapArrayPointer, _ : CCArithType) =>
                throw new TranslationException("Only addition is allowed in " +
                  "array pointer arithmetic.") // due to how AddressRange is defined: <startAddr, size>
                //addToAddressRangeStart(lhsE, rhsE, arrType, _ - _).toTerm
              case _ => lhs - rhs
            }
          case _ : AssignLeft =>
            ModuloArithmetic.bvshl(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignRight =>
            ModuloArithmetic.bvashr(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignAnd =>
            ModuloArithmetic.bvand(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignXor =>
            ModuloArithmetic.bvxor(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignOr =>
            ModuloArithmetic.bvand(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
        }), lhsE.typ, lhsE.srcInfo)
        pushVal(newVal)

        val updatingPointedValue =
          isHeapRead(lhsVal) || // *(p) = ... where p is a heap ptr
            isHeapStructFieldRead(lhsVal) // ps->f = ... where ps is a heap ptr

        if(isHeapPointer(exp, evalCtx.enclosingFunctionName) &&
           updatingPointedValue) {
          heapWrite(lhsVal.toTerm.asInstanceOf[IFunApp], newVal, true, true)
        } else {
          setValue(lookupVar(asLValue(exp.exp_1), evalCtx.enclosingFunctionName),
            getActualAssignedTerm(lhsVal, newVal),
            isIndirection(exp.exp_1)) // todo get rid of indirections?
        }
      case exp : Econdition => // exp_1 ? exp_2 : exp_3
        val srcInfo = Some(getSourceInfo(exp))
        if(evalSettings.noClausesForExprs) {
          val oldSize = clauses.size
          val cond = eval(exp.exp_1)
          val t1 = eval(exp.exp_2)
          val t2 = eval(exp.exp_3)
          if(clauses.size > oldSize)
            throw new TranslationException("This ternary expression must be " +
                                           "side effect free: " +
                                           printer.print(exp) + " at line " +
                                           srcInfo.get.line)
          // throw exceptioon if t1.typ != t2.typ
          if(t1.typ != t2.typ)
            throw new TranslationException("Unsupported operation: ternary " +
              "expression with different types: " + printer.print(exp) +
              " at line " + srcInfo.get.line)
          pushVal(CCTerm(IExpression.ite(cond.toFormula, t1.toTerm, t2.toTerm),
                         t1.typ, srcInfo))
        } else { // evalSettings.noExtraClauseForTernaryExp == false
          val cond = eval(exp.exp_1).toFormula
          saveState
          addGuard(cond)
          evalHelp(exp.exp_2)
          outputClause(Some(getSourceInfo(exp)))
          val intermediatePred = initPred

          restoreState
          addGuard(~cond)
          evalHelp(exp.exp_3)
          LocalVars.update(LocalVars.size - 1,
            new CCVar(s"ite_${srcInfo.get.line}_${srcInfo.get.col}",
                      LocalVars.last.srcInfo, LocalVars.last.typ,
                      LocalVars.last.storage))
          outputClause(intermediatePred, srcInfo)
        }
      case exp : Elor =>
        val srcInfo = Some(getSourceInfo(exp))
        evalHelp(exp.exp_1)
        maybeOutputClause(srcInfo)
        val cond = popVal.toFormula

        saveState
        addGuard(~cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause(srcInfo)

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond ||| cond2, CCInt, srcInfo))
        } else {
          outputClause(srcInfo)
          val intermediatePred = initPred

          restoreState
          addGuard(cond)
          pushVal(CCFormula(true, CCInt, srcInfo))
          outputClause(intermediatePred, srcInfo)
        }
      case exp : Eland =>
        val srcInfo = Some(getSourceInfo(exp))
        evalHelp(exp.exp_1)
        maybeOutputClause(srcInfo)
        val cond = popVal.toFormula

        saveState
        addGuard(cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause(srcInfo)

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond &&& cond2, CCInt, srcInfo))
        } else {
          outputClause(srcInfo)
          val intermediatePred = initPred

          restoreState
          addGuard(~cond)
          pushVal(CCFormula(false, CCInt, srcInfo))
          outputClause(intermediatePred, srcInfo)
        }
      case exp : Ebitor =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.BitwiseOr(lhs, rhs).expr)
      case exp : Ebitexor =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.BitwiseXor(lhs, rhs).expr)
      case exp : Ebitand =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.BitwiseAnd(lhs, rhs).expr)
      case exp : Eeq =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Equality(lhs, rhs).expr)
      case exp : Eneq =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Disequality(lhs, rhs).expr)
      case exp : Elthen =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Less(lhs, rhs).expr)
      case exp : Egrthen =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Greater(lhs, rhs).expr)
      case exp : Ele =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.LessEqual(lhs, rhs).expr)
      case exp : Ege =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.GreaterEqual(lhs, rhs).expr)
      case exp : Eleft =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.ShiftLeft(lhs, rhs).expr)
      case exp : Eright =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.ShiftRight(lhs, rhs).expr)
      case exp : Eplus =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Plus(lhs, rhs).expr)
      case exp : Eminus =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Minus(lhs, rhs).expr)
      case exp : Etimes =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Times(lhs, rhs).expr)
      case exp : Ediv =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Div(lhs, rhs).expr)
      case exp : Emod =>
        val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
        pushVal(BinaryOperators.Mod(lhs, rhs).expr)
      case exp : Etypeconv => {
        evalHelp(exp.exp_)
        pushVal(popVal convertToType getType(exp.type_name_))
      }
      case _ : Epreinc | _ : Epredec =>
        val (preExp, op) = exp match {
          case exp : Epreinc => (exp.exp_, +1)
          case exp : Epredec => (exp.exp_, -1)
        }
        evalHelp(preExp)
        val lhsVal = topVal // todo : check if necessary, maybe just use topVal?
        maybeOutputClause(Some(getSourceInfo(exp)))
        pushVal(popVal mapTerm (_ + op))
        if(isHeapPointer(preExp, evalCtx.enclosingFunctionName)) {
          heapWrite(lhsVal.toTerm.asInstanceOf[IFunApp], topVal, true, true)
        } else {
          setValue(lookupVar(asLValue(preExp), evalCtx.enclosingFunctionName),
            getActualAssignedTerm(lhsVal, topVal),
            isIndirection(preExp)) // todo get rid of indirection?
        }
      case exp : Epreop =>
        val srcInfo = Some(getSourceInfo(exp))
        evalHelp(exp.exp_)
        exp.unary_operator_ match {
          case _ : Address    =>
            topVal.toTerm match {
              case fieldFun: IFunApp
                if !(objectGetters contains fieldFun.fun) &&
                   (heap.userADTSels exists(_ contains fieldFun.fun)) => // an ADT
                val (fieldNames, rootTerm) = getFieldInfo(fieldFun)
                rootTerm match {
                  case Left(c) =>
                    val rootInd: Int = lookupVar(c.name, evalCtx.enclosingFunctionName)
                    val structType = getValue(rootInd, false).typ.asInstanceOf[CCStruct]
                    assert(rootInd > -1 && rootInd < values.size - 1) // todo
                    val ptr = CCStackPointer(rootInd, popVal.typ, structType.getFieldAddress(fieldNames))
                    pushVal(CCTerm(IExpression.Int2ITerm(rootInd), ptr, srcInfo)) //we don't care about the value
                  case Right(c) =>
                    // newAddr(alloc(h, WrappedAddr(getPtrField(getStruct(read(h, p))))))
                    // here topVal = getPtrField(getStruct(read(h, p))), we construct the rest
                    // this is to allocate memory for expressions like:
                    // &((*p)->tail)
                    // alternatively one could rewrite this using a temporary variable
                    // and create a stack pointer to it (but this needs to be done during preprocessing,
                    // otherwise when we evaluate this we would be pushing two terms instead of one)
//                    val newTerm = heapAlloc(popVal.asInstanceOf[CCTerm])
//                    assert(c.args.size == 1)
//                    val readObj = c.args.head
//                    val resSort = c.fun.asInstanceOf[MonoSortedIFunction].resSort
//                    addGuard(heap.heapADTs.hasCtor(readObj, sortCtorIdMap(resSort)))
//                    pushVal(newTerm)
                  throw new UnsupportedCFragmentException(
                    getLineStringShort(srcInfo) +
                    " Stack pointers in combination with heap pointers")
                }
              case f : IFunApp if objectGetters contains f.fun => // a heap read (might also be from a heap array)
                val readFunApp = f.args.head.asInstanceOf[IFunApp] // sth like read(h, ...)
                val Seq(heapTerm, addrTerm) = readFunApp.args
                // todo: below type extraction is not safe!
                val t = addrTerm match {
                  case IFunApp(heap.nth, args) => // if nthAddrRange(a, i)
                    val Seq(arrTerm, indTerm) = args
                    // return the addressRange starting from i
                    import heap._
                    val newTerm = addressRangeCtor(nth(arrTerm, indTerm),
                                     addrRangeSize(arrTerm) - indTerm)
                    CCTerm(newTerm,
                      getValue(arrTerm.asInstanceOf[IConstant].c.name,
                               evalCtx.enclosingFunctionName).typ, srcInfo
                    )
                  case _ =>
                    CCTerm(addrTerm, CCHeapPointer(heap,
                      getValue(addrTerm.asInstanceOf[IConstant].c.name,
                               evalCtx.enclosingFunctionName).typ), srcInfo)
                }
                popVal
                pushVal(t)

              case _ =>
                val t = if (evalCtx.handlingFunContractArgs) {
                  //val newTerm = heapAlloc(popVal.asInstanceOf[CCTerm])
                  //maybeOutputClause(Some(getSourceInfo(exp)))
                  //newTerm
                  throw new UnsupportedCFragmentException(
                    "Function contracts are currently not supported together " +
                    s"with stack pointers (${exp.line_num}:${exp.col_num})")
                } else {
                  val ind = values.indexWhere(v => v == topVal)
                  assert(ind > -1 && ind < values.size - 1) // todo
                  val ptr = CCStackPointer(ind, popVal.typ, Nil)
                  CCTerm(IExpression.Int2ITerm(ind), ptr, srcInfo)
                }
                pushVal(t) //we don't care about the value
            }
          case _ : Indirection =>
            val v = popVal
            v.typ match { // todo: type checking?
              case ptr : CCStackPointer => pushVal(getPointedTerm(ptr))
              case   _ : CCHeapPointer =>
                if(evalCtx.evaluatingLHS) pushVal(v)
                else pushVal(heapRead(v))
              case  arr : CCHeapArrayPointer =>
                if(evalCtx.evaluatingLHS) pushVal(v)
                else pushVal(heapArrayRead(v, CCTerm(IIntLit(0), CCInt, srcInfo), arr))
              case _ => throw new TranslationException("Cannot dereference " +
                  "non-pointer: " + v.typ + " " + v.toTerm)
            }
          case _ : Plus       => // nothing
          case _ : Negative   =>
            val t = popVal mapTerm (-(_))
            pushVal(CCTerm(t.toTerm, t.typ, srcInfo))
//          case _ : Complement.  Unary_operator ::= "~" ;
          case _ : Logicalneg =>
            pushVal(CCFormula(~popVal.toFormula, CCInt, srcInfo))
        }
//    case exp : Ebytesexpr.  Exp15 ::= "sizeof" Exp15;
//    case exp : Ebytestype.  Exp15 ::= "sizeof" "(" Type_name ")";
//    case exp : Earray.      Exp16 ::= Exp16 "[" Exp "]" ;

      case exp : Efunk =>
        val srcInfo = Some(getSourceInfo(exp))
        // inline the called function
        printer print exp.exp_ match {
          case "reach_error" =>
            /**
             * A special SV-COMP function used in the unreach-call category.
             * We directly rewrite this as `assert(0)`.
             */
            if(propertiesToCheck contains properties.Reachability)
              assertProperty(false, srcInfo, properties.Reachability)
            pushVal(CCFormula(true, CCInt, srcInfo))
          case name =>
            outputClause(srcInfo)
            handleFunction(name, initPred, 0)
        }

      case exp : Efunkpar =>
        val srcInfo = Some(getSourceInfo(exp))
        (printer print exp.exp_) match {
          case "assert" | "static_assert" if exp.listexp_.size == 1 =>
            val property = exp.listexp_.head match {
              case a : Efunkpar
                if uninterpPredDecls contains(printer print a.exp_) =>
                val args = a.listexp_.map(exp => atomicEval(exp, evalCtx))
                if(args.exists(a => a.typ.isInstanceOf[CCStackPointer])) {
                  throw new TranslationException(
                    getLineStringShort(srcInfo) + " Unsupported operation: " +
                    "stack pointer argument to uninterpreted predicate.")
                }
                val pred = uninterpPredDecls(printer print a.exp_)
                atom(pred, args.map(_.toTerm))
              case interpPred : Efunkpar
                if interpPredDefs contains(printer print interpPred.exp_) =>
                val args    = interpPred.listexp_.map(
                  exp => atomicEval(exp, evalCtx)).map(_.toTerm)
                val formula = interpPredDefs(printer print interpPred.exp_)
                // the formula refers to pred arguments as IVariable(index)
                // we need to subsitute those for the actual arguments
                VariableSubstVisitor(formula.f, (args.toList, 0))
              case _ =>
                atomicEvalFormula(exp.listexp_.head, evalCtx).f
            }
            assertProperty(property, srcInfo, properties.UserAssertion)
            pushVal(CCFormula(true, CCInt, srcInfo))
        case "assume" if (exp.listexp_.size == 1) =>
          val property = exp.listexp_.head match {
            case a : Efunkpar
              if uninterpPredDecls contains(printer print a.exp_) =>
              val args = a.listexp_.map(exp => atomicEval(exp, evalCtx))
                                   .map(_.toTerm)
              val pred = uninterpPredDecls(printer print a.exp_)
              atom(pred, args)
            case interpPred : Efunkpar
              if interpPredDefs contains (printer print interpPred.exp_) =>
              val args = interpPred.listexp_.map(
                exp => atomicEval(exp, evalCtx)).map(_.toTerm)
              val formula = interpPredDefs(printer print interpPred.exp_)
              // the formula refers to pred arguments as IVariable(index)
              // we need to subsitute those for the actual arguments
              VariableSubstVisitor(formula.f, (args.toList, 0))
            case _ =>
              atomicEvalFormula(exp.listexp_.head, evalCtx).f
          }
          addGuard(property)
          pushVal(CCFormula(true, CCInt, srcInfo))
        case cmd@("chan_send" | "chan_receive") if (exp.listexp_.size == 1) =>
          val name = printer print exp.listexp_.head
          (channels get name) match {
            case Some(chan) => {
              val sync = cmd match {
                case "chan_send"    => ParametricEncoder.Send(chan)
                case "chan_receive" => ParametricEncoder.Receive(chan)
              }
              outputClause(newPred(Nil, srcInfo), srcInfo, sync)
              pushVal(CCFormula(true, CCInt, srcInfo))
            }
            case None =>
              throw new TranslationException(
                name + " is not a declared channel")
          }
        case name@("malloc" | "calloc" | "alloca" | "__builtin_alloca")
          if !TriCeraParameters.parameters.value.useArraysForHeap => // todo: proper alloca and calloc
          if (!modelHeap)
            throw NeedsHeapModelException
          val (typ, allocSize) = exp.listexp_(0) match {
            case exp : Ebytestype =>
              (getType(exp), CCTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))
            //case exp : Ebytesexpr => eval(exp.exp_).typ - handled by preprocessor
            case exp : Etimes =>
              exp.exp_1 match {
                case e : Ebytestype => (getType(e), eval(exp.exp_2))
                case e if exp.exp_2.isInstanceOf[Ebytestype] =>
                  (getType(exp.exp_2.asInstanceOf[Ebytestype]), eval(e))
                case _ =>
                  throw new UnsupportedCFragmentException(
                    getLineStringShort(srcInfo) +
                    " Unsupported alloc expression: " + (printer print exp))
              }
            //case exp : Evar => // allocation in bytes
            case e : Econst => // allocation in bytes
              (CCInt, eval(e)) // todo: add support for char?

            case _ => throw new UnsupportedCFragmentException(
              getLineStringShort(srcInfo) +
              " Unsupported alloc expression: " + (printer print exp))
          }

          val arrayLoc = name match {
            case "malloc" | "calloc"           => ArrayLocation.Heap
            case "alloca" | "__builtin_alloca" => ArrayLocation.Stack
          }
          val objectTerm = CCTerm(name match {
            case "calloc"                                 => typ.getZeroInit
            case "malloc" | "alloca" | "__builtin_alloca" => typ.getNonDet
          }, typ, srcInfo)

          allocSize match {
            case CCTerm(IIntLit(IdealInt(1)), typ, srcInfo)
              if typ.isInstanceOf[CCArithType] && !evalCtx.lhsIsArrayPointer
                 && arrayLoc == ArrayLocation.Heap =>
              /**
               * global and stack arrays are allocated using CCHeapArrayPointer,
               * because CCHeapPointer does not distinguish between different
               * allocation types. This difference is needed for correctly
               * checking memory properties (e.g., only heap allocated memory
               * can be freed).
               */
              val allocatedAddr = heapAlloc(objectTerm)

              if ((propertiesToCheck contains properties.MemValidCleanup) ||
                  propertiesToCheck.contains(properties.MemValidTrack) &&
                  TriCeraParameters.get.useMemCleanupForMemTrack) {
                /**
                 * Nondeterministically write the address to the prophecy
                 * variable [[memCleanupProphecyVar]].
                 * I.e., nondet ==> prophTerm = allocatedAddr
                 */
                val prophVarInd = GlobalVars.lastIndexWhere(memCleanupProphecyVar)
                val nondetTerm = IConstant(
                  getFreshEvalVar(CCBool, None, name = "nondet").term)
                setValue(prophVarInd,
                         CCTerm(
                           IExpression.ite(
                             nondetTerm === ADT.BoolADT.True,
                             allocatedAddr.toTerm,
                             getValues(prophVarInd).toTerm
                             ), memCleanupProphecyVar.typ, None),
                         isIndirection = false)
              }

              pushVal(allocatedAddr)
            case CCTerm(sizeExp, typ, srcInfo) if typ.isInstanceOf[CCArithType] =>
              val addressRangeValue = heapBatchAlloc(objectTerm, sizeExp)
              val allocatedBlock =
                CCTerm(addressRangeValue,
                       CCHeapArrayPointer(heap, typ, arrayLoc), srcInfo)

              if (arrayLoc == ArrayLocation.Heap &&
                  ((propertiesToCheck contains properties.MemValidCleanup) ||
                   propertiesToCheck.contains(properties.MemValidTrack) &&
                   TriCeraParameters.get.useMemCleanupForMemTrack)) {
                /**
                 * Nondeterministically write the address to the prophecy
                 * variable [[memCleanupProphecyVar]]. Here a corner case to
                 * consider is when sizeExp is not > 0, in which case no memory
                 * is allocated, hence no need to change the value of the
                 * prophecy variable.
                 * I.e., (nondet & sizeExp > 0) ==> prophTerm = allocatedAddr
                 */
                val prophVarInd = GlobalVars.lastIndexWhere(memCleanupProphecyVar)
                val nondetTerm  = IConstant(
                  getFreshEvalVar(CCBool, None, name = "nondet").term)
                setValue(prophVarInd,
                         CCTerm(
                           IExpression.ite(
                             nondetTerm === ADT.BoolADT.True & sizeExp > 0,
                             heap.nth(allocatedBlock.toTerm, 0),
                             getValues(prophVarInd).toTerm
                             ), memCleanupProphecyVar.typ, None),
                         isIndirection = false)
              }
              pushVal(allocatedBlock)
            // case CCTerm(IIntLit(IdealInt(n)), CCInt) =>
                // todo: optimise constant size allocations > 1?
          }
        case name@("malloc" | "calloc" | "alloca" | "__builtin_alloca")
          if TriCeraParameters.parameters.value.useArraysForHeap =>
          /**
           * @todo Support checking [[properties.MemValidCleanup]] when using
           *       arrays to model heaps.
           */

          val (typ, allocSize) = exp.listexp_(0) match {
            case exp : Ebytestype =>
              (getType(exp), CCTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))
            //case exp : Ebytesexpr => eval(exp.exp_).typ - handled by preprocessor
            case exp : Etimes =>
              exp.exp_1 match {
                case e : Ebytestype => (getType(e), eval(exp.exp_2))
                case e if exp.exp_2.isInstanceOf[Ebytestype] =>
                  (getType(exp.exp_2.asInstanceOf[Ebytestype]), eval(e))
                case _ =>
                  throw new UnsupportedCFragmentException(
                    "Unsupported alloc expression: " + (printer print exp))
              }
            //case exp : Evar => // allocation in bytes

            case _ => throw new UnsupportedCFragmentException(
              "Unsupported alloc expression: " + (printer print exp))
          }

          val (sizeExpr, sizeInt) = allocSize match {
            case CCTerm(IIntLit(IdealInt(n)), typ, srcInfo)
              if typ.isInstanceOf[CCArithType] && !evalCtx.lhsIsArrayPointer =>
              (Some(allocSize), Some(n))
            case _ =>
              (Some(allocSize), None)
          }
          val arrayLocation = name match {
            case "malloc" | "calloc"           => ArrayLocation.Heap
            case "alloca" | "__builtin_alloca" => ArrayLocation.Stack
          }

          val theory = ExtArray(Seq(CCInt.toSort), typ.toSort) // todo: only 1-d int arrays...
          val arrType = CCArray(typ, sizeExpr, sizeInt, theory, arrayLocation)

          val arrayTerm = CCTerm(name match {
            case "calloc"                                 => arrType.getZeroInit
            case "malloc" | "alloca" | "__builtin_alloca" => arrType.getNonDet
          }, arrType, srcInfo)

          pushVal(arrayTerm)
        case "realloc" =>
          if (!modelHeap)
            throw NeedsHeapModelException
          throw new TranslationException("realloc is not supported.")
        case "free" =>
          if (!modelHeap)
            throw NeedsHeapModelException
          val ptrExpr = atomicEval(exp.listexp_.head, evalCtx)
          heapFree(ptrExpr, srcInfo)
          pushVal(CCTerm(0, CCVoid, srcInfo)) // free returns no value, push dummy
        case name =>
          // then we inline the called function

          // evaluate the arguments
          // todo: if we are to handle a function contract, arguments are handled
          // as heap pointers. if the function is to be inlined, then arguments
          // are handled as stack pointers. here we set a flag to notify this
          val handlingFunctionContractArgs = functionContexts.contains(name)
          val newEvalCtx = evalCtx
            .withHandlingFunContractArgs(handlingFunctionContractArgs)
            .incrementCallDepth
          for (e <- exp.listexp_)
            evalHelp(e)(evalSettings, newEvalCtx.withFunctionName(name))

          // substitute fresh variable names (e.g., __eval) with actual function argument names
          val argCount = exp.listexp_.size
          val argNames = functionDefs get name match {
            case Some(f) => getFunctionArgNames(f)
            case None =>
              uninterpPredDecls get name match {
                case Some(predDecl) =>
                  predDecl.argVars.map(_.name)
                case None => Nil
              }
          }
          if(argNames nonEmpty) {
            val evalVars = LocalVars.getVarsInTopFrame.takeRight(argCount)
            LocalVars.pop(argCount) // remove those vars
            assert(argNames.length == argCount && evalVars.length == argCount)
            val newVars = if (((assertionClauses.map(_.clause.constants) ++
              clauses.flatMap(_._1.constants)) intersect evalVars.map(_.term)).nonEmpty) {
              // todo: replace terms by substituting them if they were added to clauses too!
              evalVars
            } else {
              for ((oldVar, argName) <- evalVars zip argNames) yield {
                val uniqueArgName =
                  if (LocalVars.vars.exists(v => v.name == argName)) name + "_" + argName
                  else argName
                new CCVar(uniqueArgName, oldVar.srcInfo, oldVar.typ,
                          oldVar.storage)
              }
            }
            newVars.foreach(LocalVars addVar)
          }
          //////////////////////////////////////////////////////////////////////

          /**
           * @todo Below might be buggy and break when there is more than
           *       one nested call
           */
          if(!handlingFunctionContractArgs || evalCtx.nestedCallDepth == 0)
            outputClause(Some(getSourceInfo(exp)))

          val functionEntry = initPred

          handleFunction(name, functionEntry, argCount)
      }

      case exp : Eselect =>
        val srcInfo = Some(getSourceInfo(exp))
        val subexpr = eval(exp.exp_)(evalSettings,
                                     evalCtx.withEvaluatingLHS(false))
        val rawFieldName = exp.cident_
        subexpr.typ match {
          case structType : CCStruct => // todo a better way
            if(!structType.contains(rawFieldName))
              throw new TranslationException(rawFieldName + " is not a member of "
                + structType + "!")
            val ind = structType.getFieldIndex(rawFieldName)
            val fieldType = structType.getFieldType(ind)
            val sel = structType.getADTSelector(ind)
            pushVal(CCTerm(sel(subexpr.toTerm), fieldType, srcInfo))
          case _ =>
            throw new TranslationException("Trying to access field '." +
              rawFieldName + "' of a variable which is not a struct.")
        }

      case exp : Epoint =>
        val srcInfo = Some(getSourceInfo(exp))
        val subexpr = eval(exp.exp_)(evalSettings,
                                     evalCtx.withEvaluatingLHS(false))
        val rawFieldName = exp.cident_
        val term = subexpr.typ match {
          case ptrType : CCStackPointer => getPointedTerm(ptrType)
          case _ : CCHeapPointer =>  //todo: error here if field is null
            heapRead(subexpr)
          case _ => throw new TranslationException(
            "Trying to access field '->" + rawFieldName + "' of non pointer.")
        }
        val structType = term.typ match {
          case typ : CCStruct => typ
          case CCStructField(name, structs) => structs(name)
          case typ => throw new TranslationException("Epoint is currently " +
            "only implemented for structs, not " + typ + ": " +
            (printer print exp))
        }
        val structInfo = structInfos.find(_.name == structType.shortName) match {
          case Some(info) => info
          case None => throw new TranslationException(
            s"Internal error: could not find struct ${structType.shortName} in structInfos.")
        }
        if(!structType.contains(rawFieldName))
          throw new TranslationException(rawFieldName + " is not a member of "
            + structType + "!")
        val ind = structType.getFieldIndex(rawFieldName)
        val fieldType = structType.getFieldType(ind)
        val sel = structType.getADTSelector(ind)
        pushVal(CCTerm(sel(term.toTerm), fieldType, srcInfo))

      case _ : Epostinc | _ : Epostdec=>
        val (postExp, op) = exp match {
          case exp : Epostinc => (exp.exp_, +1)
          case exp : Epostdec => (exp.exp_, -1)
        }
        evalHelp(postExp)
        val evalExp = topVal
        maybeOutputClause(Some(getSourceInfo(exp)))
        if(isHeapPointer(postExp, evalCtx.enclosingFunctionName)) {
          heapWrite(evalExp.toTerm.asInstanceOf[IFunApp], topVal.mapTerm(_ + op),
            assertMemSafety = true,
            assumeMemSafety = true)
        } else {
          setValue(lookupVar(asLValue(postExp), evalCtx.enclosingFunctionName),
            getActualAssignedTerm(evalExp, topVal.mapTerm(_ + op)),
            isIndirection(postExp)) // todo get rid of indirection?
        }

      case exp : Evar =>
        val name = exp.cident_
        pushVal(lookupVarNoException(name, evalCtx.enclosingFunctionName) match {
          case -1 =>
            (enumeratorDefs get name) match {
              case Some(e) => e
              case None => throw new TranslationException(
                getLineString(exp) + "Symbol " + name + " is not declared")
            }
          case ind =>
            getValue(ind, false)
        })

      case exp : Econst => evalHelp(exp.constant_)
      case exp : Estring => // todo: implement this properly
        warn("ignoring string argument")
        val srcInfo = Some(getSourceInfo(exp))
        pushVal(CCTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))

      case exp : Earray =>
        val srcInfo = Some(getSourceInfo(exp))
        val arrayTerm : CCExpr = eval(exp.exp_1)
        val index : CCExpr = eval(exp.exp_2)

        import IExpression._
        arrayTerm.typ match {
          case array : CCHeapArrayPointer =>
            pushVal(heapArrayRead(arrayTerm, index, array))
          case array : CCArray => // todo: move to separate method
            val readValue = CCTerm(array.arrayTheory.
              select(arrayTerm.toTerm, index.toTerm), array.elementType, srcInfo)
            array.sizeExpr match {
              case Some(expr)
                if propertiesToCheck contains properties.MemValidDeref =>
                assertProperty((index.toTerm >= 0) &&&
                  (index.toTerm < expr.toTerm), srcInfo,
                               properties.MemValidDeref)
              case _ => // no safety assertion needed for mathematical arrays
            }
            pushVal(readValue)
          case _ =>
            throw new TranslationException(getLineString(exp) +
              arrayTerm + " is not a supported array type - currently only " +
                                           "1-d arrays are supported.")
        }

      case _ =>
        throw new TranslationException(getLineString(exp) +
          "Expression currently not supported by TriCera: " +
          (printer print exp))
    }

    private def handleFunction(name : String,
                               functionEntry : CCPredicate,
                               argCount : Int) =
      functionContexts get name match {
        case Some(ctx) =>
          // use the contract of the function
//          assert(!(pointerArgs exists (_.isInstanceOf[CCStackPointer])),
//                 "function contracts do not support pointer arguments yet")

          val funDef = functionDefs(name)

          var argTerms : List[ITerm] = List()
          for (_ <- 0 until argCount)
            argTerms = popVal.toTerm :: argTerms

          val postGlobalVars : Seq[ITerm] = // todo : use ctx postglobal?
            for (v <- GlobalVars.vars) yield {
              if (v.isStatic) {
                throw new TranslationException(
                  "Static variables with contracts are not supported yet.")
                  // todo: this should be easy to support, need to distinguish
                  //       at a few locations the static variables belonging to
                  //       that function only.
              }
              IExpression.i(v.sort newConstant(v.name + "_post")) //
              // todo: refactor
            }

          val globals : Seq[ITerm] =
            for (n <- 0 until GlobalVars.size)
            yield getValue(n, false).toTerm

          val prePredArgs : Seq[ITerm] = globals ++ argTerms

          val resVar : Seq[CCVar] = getResVar(getType(funDef))
          val postPredArgs : Seq[ITerm] =
            prePredArgs ++ postGlobalVars ++ resVar.map(c => IConstant(c.term))
            //postGlobalVars ++ argTerms ++ globals ++ resVar.map(c => IConstant(c.term))

          val preAtom  = ctx.prePred(prePredArgs)
          val postAtom = ctx.postPred(postPredArgs)

          assertProperty(preAtom, functionEntry.srcInfo,
                         properties.FunctionPrecondition(name,functionEntry.srcInfo))

          addGuard(postAtom)

          for (((c, t), n) <- (postGlobalVars.iterator zip
                                 GlobalVars.formalTypes.iterator).zipWithIndex)
            setValue(n, CCTerm(c, t, None), false) // todo: srcInfo?

          resVar match {
            case Seq(v) => pushVal(CCTerm(v.term, v.typ, v.srcInfo))
            case Seq()  => pushVal(CCTerm(0, CCVoid, None)) // push a dummy result
          }
        case None =>
          uninterpPredDecls get name match {
            case Some(predDecl) =>
              //val argNames = PredPrintContextPrintContext.predArgNames(predDecl.pred)
              var argTerms : List[ITerm] = List()
              for (_ <- 0 until argCount) {
                argTerms = popVal.toTerm :: argTerms
              }
              pushVal(CCFormula(predDecl(argTerms), CCInt, None)) // todo:srcInfo
            case None =>
              val args =
                (for (_ <- 0 until argCount) yield popVal.typ).toList.reverse
              // get rid of the local variables, which are later
              // replaced with the formal arguments
              // pointer arguments are saved and passed on
              callFunctionInlining(name, functionEntry, args)
          }
      }

    private def callFunctionInlining(name : String,
                                     functionEntry : CCPredicate,
                                     pointerArgs : List[CCType] = Nil) =
      (functionDefs get name) match {
        case Some(fundef) =>
          val typ = getType(fundef)
          val isNoReturn = typ == CCVoid
          val exitVar =
            if (isNoReturn) Nil
            else List(new CCVar("_" + name + "Ret", None, typ, AutoStorage)) // todo: return line no?
          val srcInfo = Some(FuncDef(fundef).sourceInfo)
          val functionExit = newPred(exitVar, srcInfo) // todo: return line no?

          inlineFunction(fundef, functionEntry, functionExit, pointerArgs,
            isNoReturn, name)

          // reserve an argument for the function result

          if (typ == CCVoid)
            pushFormalVal(CCInt, srcInfo)
          else
            pushFormalVal(typ, srcInfo)
          resetFields(functionExit)
        case None => (functionDecls get name) match {
          case Some((fundecl, typ)) =>
            if (!(name contains "__VERIFIER_nondet" ))
              warn("no definition of function \"" + name + "\" available")
            pushFormalVal(typ, Some(getSourceInfo(fundecl)))
          case None =>
            throw new TranslationException(
              "Function " + name + " is not declared")
        }
      }

    private def checkPointerIntComparison(t1 : CCExpr, t2 : CCExpr) :
      (CCExpr, CCExpr) = {
      (t1.typ, t2.typ) match {
        case (_ : CCHeapPointer, _ : CCArithType) =>
          if (t2.toTerm != IIntLit(IdealInt(0)))
            throw new TranslationException("Pointers can only compared with `null` or `0`. " +
                                           getLineString(t2.srcInfo))
          else
            (t1, CCTerm(heap.nullAddr(), t1.typ, t1.srcInfo)) // 0 to nullAddr()
        case (_: CCArithType, _: CCHeapPointer) =>
          if (t1.toTerm != IIntLit(IdealInt(0)))
            throw new TranslationException("Pointers can only compared with `null` or `0`. " +
                                           getLineString(t2.srcInfo))
          else
            (CCTerm(heap.nullAddr(), t2.typ, t2.srcInfo), t2) // 0 to nullAddr()
        case _ => (t1, t2)
      }
    }

    private def evalBinExpArgs(left : Exp, right : Exp)
                        (implicit evalSettings : EvalSettings,
                                  evalContext  : EvalContext) :
    (CCExpr, CCExpr) = {
      val (lhs, rhs) =
        if (evalSettings.noClausesForExprs) {
          (eval(left), eval(right))
        } else {
          evalHelp(left)
          maybeOutputClause(Some(getSourceInfo(left)))
          evalHelp(right)
          val rhs = popVal
          val lhs = popVal
          (lhs, rhs)
        }
      checkPointerIntComparison(lhs, rhs)
    }

    ////////////////////////////////////////////////////////////////////////////

    private def evalHelp(constant : Constant) : Unit = {
      val srcInfo = Some(getSourceInfo(constant))
      constant match {
//      case constant : Efloat.        Constant ::= Double;
        case constant : Echar =>
          pushVal(CCTerm(IdealInt(constant.char_.toInt), CCInt, srcInfo))
        case constant : Eunsigned =>
          pushVal(CCTerm(IdealInt(
            constant.unsigned_.substring(
              0, constant.unsigned_.size - 1)), CCUInt, srcInfo))
        case constant : Elong =>
          pushVal(CCTerm(IdealInt(
            constant.long_.substring(
              0, constant.long_.size - 1)), CCLong, srcInfo))
        case constant : Eunsignlong =>
          pushVal(CCTerm(IdealInt(
            constant.unsignedlong_.substring(
              0, constant.unsignedlong_.size - 2)), CCULong, srcInfo))
        case constant : Ehexadec =>
          pushVal(CCTerm(IdealInt(
            constant.hexadecimal_ substring 2, 16), CCInt, srcInfo))
        case constant : Ehexaunsign =>
          pushVal(CCTerm(IdealInt(constant.hexunsigned_.substring(
            2, constant.hexunsigned_.size - 1), 16), CCUInt, srcInfo))
        case constant : Ehexalong =>
          pushVal(CCTerm(IdealInt(constant.hexlong_.substring(
            2, constant.hexlong_.size - 1), 16), CCLong, srcInfo))
        case constant : Ehexaunslong =>
          pushVal(CCTerm(IdealInt(constant.hexunslong_.substring(
            2, constant.hexunslong_.size - 2), 16), CCULong, srcInfo))
        case constant : Eoctal =>
          pushVal(CCTerm(IdealInt(constant.octal_, 8), CCInt, srcInfo))
//      case constant : Eoctalunsign.  Constant ::= OctalUnsigned;
        case constant : Eoctallong =>
          pushVal(CCTerm(IdealInt(constant.octallong_.substring(
            0, constant.octallong_.size - 1), 8), CCLong, srcInfo))
//      case constant : Eoctalunslong. Constant ::= OctalUnsLong;
//      case constant : Ecdouble.      Constant ::= CDouble;
//      case constant : Ecfloat.       Constant ::= CFloat;
//      case constant : Eclongdouble.  Constant ::= CLongDouble;
        case constant : Eint =>
          pushVal(CCTerm(IExpression.i(IdealInt(
            constant.unboundedinteger_)), CCInt, srcInfo))
        case constant => throw new TranslationException(
          "Unimplemented type: " + constant.getClass)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def inlineFunction(functionDef : Function_def,
                             entry : CCPredicate,
                             exit : CCPredicate,
                             args : List[CCType],
                             isNoReturn : Boolean,
                             functionName : String) : Unit = {
    LocalVars pushFrame
    val stm = pushArguments(functionDef, args)

    // this might be an inlined function in an expression where we need to
    // carry along other terms that were generated in the expression, so this
    // assertion is not necessarily true:
    // assert(entry.arity == allFormalVars.size)

    val translator = FunctionTranslator(exit, functionName)
    val finalPred =
      if (isNoReturn) {
        translator.translateNoReturn(stm, entry)
        exit
      } else
        translator.translateWithReturn(stm, entry)
    LocalVars popFrame
  }

  private def createHeapPointer(decl : BeginPointer, typ : CCType) :
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

  private def getFunctionArgNames(functionDef : Function_def) : Seq[String] = {
    val f = FuncDef(functionDef)
    val decl = f.decl match {
      case noPtr : NoPointer => noPtr.direct_declarator_
      case ptr   : BeginPointer => ptr.direct_declarator_
    }
    decl match {
      case dec : NewFuncDec =>
        val decList = dec.parameter_type_.asInstanceOf[AllSpec]
          .listparameter_declaration_
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
        argNames
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
          .listparameter_declaration_
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
                        Seq(CCInt.toSort), typ.toSort), ArrayLocation.Heap)
                    case _ => typ
                  }
                case _ => typ
              }
              val declaredVar =
                new CCVar(name, Some(getSourceInfo(argDec)), actualType, AutoStorage)
              LocalVars addVar declaredVar

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
              LocalVars addVar declaredVar
              processHints(argDec.listannotation_)
//            case argDec : Abstract =>
          }
//      case dec : OldFuncDef =>
//        for (ident <- dec.listcident_)
//          LocalVars += new ConstantTerm(ident)
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
                         stm : Expression_stm) : (Symex, Option[CCExpr]) = {
      val exprSymex = Symex(initPred)
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
      output(addRichClause(Clause(atom(rp, allFormalVarTerms take rp.arity),
                    List(atom(finalPred, allFormalVarTerms  take finalPred.arity)),
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
      //output(Clause(atom(rp, (allFormalVars take (rp.arity - 1)) ++
      //                       List(IConstant(new ConstantTerm("__result")))),
      //              List(atom(finalPred, allFormalVars)),
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
      //output(Clause(atom(rp, (allFormalVars take (rp.arity - 1)) ++
      //                       List(IConstant(new ConstantTerm("__result")))),
      //              List(atom(finalPred, allFormalVars)),
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
      clauses reduceToSize offset

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
      new ArrayBuffer[(String, CCPredicate, Seq[ITerm], Int, SourceInfo)]
    private val labelledLocs =
      new MHashMap[String, (CCPredicate, Seq[ITerm])]
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
        case Seq(MaybeACSLAnnotation(annot, _)) =>
          val stmSymex = Symex(entry)
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
                    case Some(args) => Some(CCTerm(args(i), v.typ, v.srcInfo))
                    case None => None
                  }
                case None => None
              }
            }

            override def getGlobals: Seq[CCVar] = GlobalVars.vars
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
                case p: CCHeapPointer => p.typ
                case t => t
              }
            override def isHeapEnabled: Boolean = modelHeap
            override def getHeap: HeapObj =
              if (modelHeap) heap
              else throw new TranslationException("getHeap called with no heap!")
            override def getHeapTerm: ITerm =
              if (modelHeap)
                stmSymex.getValues(GlobalVars.lastIndexWhere(heapVar)).toTerm
              else throw new TranslationException("getHeapTerm called with no heap!")
            override def getOldHeapTerm: ITerm = {
              if (modelHeap) getHeapTerm
              else throw new TranslationException("getOldHeapTerm called with no heap!")
            } // todo: heap term for exit predicate?

            override val getStructMap: Map[IFunction, CCStruct] = 
              structDefs.values.toSet.map((struct: CCStruct) => (struct.ctor, struct)).toMap

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
        case Seq(MaybeACSLAnnotation(annot, _)) =>
          val stmSymex = Symex(entry)
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
                    case Some(args) => Some(CCTerm(args(i), v.typ, v.srcInfo))
                    case None       => None
                  }
                case None         => None
              }
            }

            override def getGlobals : Seq[CCVar] = GlobalVars.vars
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
            override def getHeapTerm : ITerm =
              if (modelHeap)
                stmSymex.getValues(GlobalVars.lastIndexWhere(heapVar)).toTerm
              else throw NeedsHeapModelException
            override def getOldHeapTerm : ITerm =
              getHeapTerm // todo: heap term for exit predicate?
            
            override val getStructMap: Map[IFunction, CCStruct] = 
              structDefs.values.toSet.map((struct: CCStruct) => (struct.ctor, struct)).toMap

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
      val decSymex = Symex(entry)
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
        labelledLocs.put(stm.cident_, (entry, allFormalVarTerms))
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
        output(addRichClause(Clause(atom(exit, allVarInits take exit.arity),
                                    List(), globalPreconditions),
          Some(getSourceInfo(compound)))
        )
      case compound : ScompTwo => {
        LocalVars pushFrame

        val stmsIt = ap.util.PeekIterator(compound.liststm_.iterator)

        // merge simple side-effect-free declarations with
        // the entry clause
        var entryPred = newPred(Nil,
          if(stmsIt.hasNext) Some(getSourceInfo(stmsIt.peekNext)) else None)
        var entryClause =
          Clause(atom(entryPred, allVarInits take entryPred.arity), List(), globalPreconditions)

        while (stmsIt.hasNext && isSEFDeclaration(stmsIt.peekNext)) {
          val decSymex = Symex(entryPred)
          collectVarDecls(stmsIt.next.asInstanceOf[DecS].dec_,
                          false, decSymex, "", false)
          val srcInfo = entryPred.srcInfo // todo: correct srcInfo?
          entryPred = newPred(Nil,
            if(stmsIt.hasNext) Some(getSourceInfo(stmsIt.peekNext)) else None) // todo: correct?
          entryClause = merge((decSymex genClause(entryPred, srcInfo)).clause, entryClause)
        }
        output(addRichClause(entryClause, entryPred.srcInfo))

        translateStmSeq(stmsIt, entryPred, exit)
        LocalVars popFrame
      }
    }

    private def isSEFDeclaration(stm : Stm) : Boolean = stm match {
      case stm: DecS => {
        stm.dec_ match {
          case _ : NoDeclarator => true
          case dec : Declarators =>
            dec.listinit_declarator_ forall {
              case _ : OnlyDecl => true
              case _ : HintDecl => true
              case decl : InitDecl => isSEFInitializer(decl.initializer_)
              case decl : HintInitDecl =>
                decl.initializer_.asInstanceOf[InitExpr].exp_ match {
                  case _ : Econst => true
                  case _ => false
                }
            }
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
        val vars = allFormalVarTerms
        output(addRichClause(Clause(atom(exit, vars take exit.arity),
                                    List(atom(entry, vars take entry.arity)), true),
          Some(getSourceInfo(compound))))
      }
      case compound : ScompTwo => {
        LocalVars pushFrame

        val stmsIt = compound.liststm_.iterator
        translateStmSeq(stmsIt, entry, exit)
        LocalVars popFrame
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
                atom(exit, allFormalVarTerms take exit.arity),
                List(atom(prevPred, allFormalVarTerms take prevPred.arity)),
                true), srcInfo))
            }
          }
          case stm => {
            val srcInfo = Some(getSourceInfo(stm))
            var nextPred = if (stmsIt.hasNext) newPred(Nil, None) // todo: line no?
                           else exit
            translate(stm, prevPred, nextPred)
            prevPred = nextPred
          }
        }
    }

    type SwitchCaseCollector = ArrayBuffer[(CCExpr, CCPredicate)]

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
        val condSymex = Symex(entry)
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

        val condSymex = Symex(first)
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
              first(allFormalVars) :- third(allFormalVarTerms), srcInfo))
          case stm : SiterFour  => {
            val incSymex = Symex(third)
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
        val condSymex = Symex(entry)
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
        val vars = allFormalVarTerms

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
        val selectorSymex = Symex(entry)
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

        defaults match {
          case Seq() =>
            // add an assertion that we never try to jump to a case that
            // does not exist. TODO: add a parameter for this?
            selectorSymex assertProperty(
              or(guards), Some(getSourceInfo(stm)),
              properties.SwitchCaseValidJump)
          case Seq((_, target)) => {
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
      case jump : SjumpOne => { // goto
        jumpLocs += ((jump.cident_, entry, allFormalVarTerms, clauses.size,
          getSourceInfo(jump)))
        // reserve space for the later jump clause
        output(new CCClause(null, null))
      }
      case jump : SjumpTwo => { // continue
        if (innermostLoopCont == null)
          throw new TranslationException(
            "\"continue\" can only be used within loops")
        Symex(entry) outputClause(innermostLoopCont, srcInfo)
      }
      case jump : SjumpThree => { // break
        if (innermostLoopExit == null)
          throw new TranslationException(
            "\"break\" can only be used within loops")
        Symex(entry) outputClause(innermostLoopExit, srcInfo)
      }
      case jump : SjumpFour => // return
        returnPred match {
          case Some(rp) => {
            var nextPred = entry
            val args = allFormalVarTerms take rp.arity
            output(addRichClause(Clause(atom(rp, args),
                          List(atom(nextPred, allFormalVarTerms take nextPred.arity)),
                          true), srcInfo))
          }
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      case jump : SjumpFive => { // return exp
        val symex = Symex(entry)
        implicit val evalSettings = symex.EvalSettings()
        implicit val evalContext  = symex.EvalContext()
                                         .withFunctionName(functionName)
        val retValue = symex eval jump.exp_
        returnPred match {
          case Some(rp) =>
            val args = (symex.getValuesAsTerms take (rp.arity - 1)) ++
                       List(retValue.toTerm)
            symex outputClause(atom(rp, args), srcInfo)
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      }
      case _ : SjumpAbort | _ : SjumpExit => // abort() or exit(int status)
        output(addRichClause(
          Clause(atom(globalExitPred, allFormalVarTerms take globalExitPred.arity),
                 List(atom(entry, allFormalVarTerms take entry.arity)),
                 true), srcInfo))
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
            val entrySymex = Symex(entry)
            entrySymex outputClause(first, srcInfo)
            translate(stm.stm_, first, exit)
          }
          atomicBlocks += ((currentClauseNum, clauses.size))
        }
        case stm : SatomicTwo => {
          val currentClauseNum = clauses.size
          inAtomicMode {
            val first = newPred(Nil, srcInfo)
            val condSymex = Symex(entry)
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
              (cond :- atom(entry, allFormalVarTerms take entry.arity))
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
      (for (p <- ParametricEncoder.allPredicates(processes).iterator;
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
                               GlobalVars.size
                             },
                             None,
                             if (useTime)
                               ParametricEncoder.ContinuousTime(0, 1)
                             else
                               ParametricEncoder.NoTime,
                             timeInvariants,
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
          (p => "inv_" + p._1.name == pred.name) match {
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
    def predArgNames (pred : Predicate) : Seq[String] =
      getPred(pred).argVars.map(_.toString)
    def predSrcInfo (pred : Predicate) : Option[SourceInfo] =
      getPred(pred).srcInfo
    def isUninterpretedPredicate (predicate : Predicate) : Boolean =
      uninterpPredDecls.values.exists(ccPred => ccPred.pred == predicate)
  }
}
