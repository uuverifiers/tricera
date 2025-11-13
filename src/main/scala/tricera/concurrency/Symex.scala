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

import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.{ExtArray, ModuloArithmetic}
import ap.types.{MonoSortedIFunction, SortedConstantTerm}
import hornconcurrency.ParametricEncoder
import lazabs.horn.abstractions.VerificationHints.VerifHintInitPred
import lazabs.horn.bottomup.HornClauses
import tricera.Util._
import tricera.concurrency.CCReader._
import tricera.concurrency.ccreader._
import tricera.concurrency.ccreader.CCExceptions._
import tricera.concurrency.concurrent_c.Absyn._
import tricera.Literals
import tricera.params.TriCeraParameters
import tricera.properties
import IExpression.toFunApplier
import tricera.concurrency.ccreader.CCBinaryExpressions.BinaryOperators
import tricera.concurrency.heap.HeapModel

import scala.jdk.CollectionConverters._
import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, Stack}

object Symex {
  def apply(context        : SymexContext,
            scope          : CCScope,
            initPred       : CCPredicate,
            maybeHeapModel : Option[HeapModel]) : Symex = {
    new Symex(context, scope, initPred, maybeHeapModel)
  }

  // These need to be here for now as we create many Symexes...
  private val locationMap = mutable.Map[SourceInfo, Int]()
  private var locationCounter = 0
}

class Symex private (context        : SymexContext,
                     scope          : CCScope,
                     oriInitPred    : CCPredicate,
                     maybeHeapModel : Option[HeapModel]) {
  private var values : scala.Seq[CCTerm] =
    scope.allFormalVars.map(v => CCTerm.fromTerm(v.term, v.typ, v.srcInfo))
  private var guard : IFormula = true
  private var touchedGlobalState : Boolean = false
  private var assignedToStruct : Boolean = false
  private var calledFunction : Boolean = false

  private implicit def toRichTerm(expr : CCTerm) :
  Object{def mapTerm(m:ITerm => ITerm) : CCTerm} = new Object {
    def mapTerm(m : ITerm => ITerm) : CCTerm =
      // TODO: type promotion when needed
      CCTerm.fromTerm(expr.typ cast m(expr.toTerm), expr.typ, expr.srcInfo)
  }

  def addGuard(f : IFormula) : Unit = {
    guard = guard &&& f
    touchedGlobalState =
      touchedGlobalState || !scope.freeFromGlobal(f)
  }

  def getGuard = guard

  private var initAtom =
    if (oriInitPred == null)
      null
    else
      context.atom(oriInitPred, scope.allFormalVarTerms take oriInitPred.arity)
  private def initPred = context.predCCPredMap(initAtom.pred)

  def initAtomArgs = if(initAtom != null) Some(initAtom.args) else None

  private val savedStates = new Stack[(IAtom, scala.Seq[CCTerm], IFormula, /*IFormula,*/ Boolean, Boolean, Boolean)]
  def saveState =
    savedStates push ((initAtom, values.toList, guard, touchedGlobalState, assignedToStruct, calledFunction))
  def restoreState = {
    val (oldAtom, oldValues, oldGuard, /*oldPullGuard,*/ oldTouched, oldAssignedToStruct, oldCalledFunction) = savedStates.pop
    initAtom = oldAtom
    values = oldValues
    scope.LocalVars.pop(scope.LocalVars.size - values.size + scope.GlobalVars.size)
    guard = oldGuard
    touchedGlobalState = oldTouched
    assignedToStruct = oldAssignedToStruct
    calledFunction = oldCalledFunction
  }

  def atomValuesUnchanged = {
    val (oldAtom, oldValues, _, _, _, _) = savedStates.top
    initAtom == oldAtom &&
    ((values.iterator zip oldValues.iterator) forall {
      case (x, y) => x == y
    })
  }

  private def maybeOutputClause(srcInfo : Option[SourceInfo]) : Unit =
    if ((!context.atomicMode && touchedGlobalState)
        || assignedToStruct || calledFunction)
      outputClause(srcInfo)

  private def pushVal(v : CCTerm, varName : String = "") = {
    val freshVar = scope.getFreshEvalVar(v.typ, v.srcInfo, varName)
    addValue(v)
    // reserve a local variable, in case we need one later
    scope.LocalVars.addVar(freshVar)

    if (context.usingInitialPredicates) {
      // if the pushed value refers to other variables,
      // add initial predicates that relate the values of
      // temporary variables with the original variables
      //
      // TODO: this is currently not very effective ...

      val varMapping =
        (for (d <- v.occurringConstants.iterator;
              index = scope.lookupVarNoException(d.name, "")) // TODO: can probably specify enclosing function?
        yield (d -> index)).toMap

      if (varMapping forall { case (_, ind) => ind >= 0 }) {
        val defTerm =
          ConstantSubstVisitor(v.toTerm,
                               varMapping.view.mapValues(IExpression.v(_)).toMap)
        val rhs = IExpression.v(scope.variableHints.size - 1)

        if (defTerm != rhs) {
          val defEq = defTerm === rhs
          scope.variableHints(scope.variableHints.size - 1) =
            List(VerifHintInitPred(defEq))
        }
      }
    }
  }

  private def pushFormalVal(typ : CCType, srcInfo : Option[SourceInfo]) = {
    val freshVar = scope.getFreshEvalVar(typ, srcInfo)
    scope.LocalVars.addVar(freshVar)
    addValue(CCTerm.fromTerm(freshVar.term, typ, srcInfo))
    addGuard(freshVar rangePred)
  }

  private def popVal = {
    val res = values.last
    values = values.init
    scope.LocalVars.pop(1)
    res
  }
  private def topVal = values.last

  private def outputClause(srcInfo : Option[SourceInfo]) : Unit =
    outputClause(context.newPred(Nil, srcInfo), srcInfo)

  def genClause(pred : CCPredicate,
                srcInfo : Option[SourceInfo]) : CCClause = {
    import HornClauses._
    if (initAtom == null)
      throw new TranslationException("too complicated initialiser")
    val clause = asAtom(pred) :- (initAtom &&& guard)
    context.addRichClause(clause, srcInfo)
  }

  def outputClause(pred : CCPredicate,
                   srcInfo : Option[SourceInfo],
                   sync : ParametricEncoder.Synchronisation =
                   ParametricEncoder.NoSync) : Unit = {
    val c = genClause(pred, srcInfo)
    if (!c.clause.hasUnsatConstraint)
      context.output(c, sync)
    resetFields(pred)
  }

  def outputClause(headAtom : IAtom,
                   srcInfo : Option[SourceInfo]) : Unit = {
    import HornClauses._
    val clause = headAtom :- (initAtom &&& guard)
    if (!clause.hasUnsatConstraint)
      context.output(context.addRichClause(clause, srcInfo))
  }

  def resetFields(pred : CCPredicate) : Unit = {
    initAtom = context.atom(pred, scope.allFormalVarTerms take pred.arity)
    guard = true
    touchedGlobalState = false
    assignedToStruct = false
    calledFunction = false
    for ((e, i) <- scope.allFormalCCTerms.iterator.zipWithIndex) {
      values = values.updated(i, e)
    }
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
    context.addAssertion(
      context.mkRichAssertionClause(clause, srcInfo, propertyType))
  }

  def addValue(t : CCTerm) = {
    values = values ++ scala.Seq(t)
    touchedGlobalState = touchedGlobalState || !scope.freeFromGlobal(t)
  }

  private def getValue(name : String,
                       enclosingFunction : String,
                       isIndirection : Boolean = false) : CCTerm =
    getValue(scope.lookupVar(name, enclosingFunction), isIndirection)
  private def getValue(ind : Int,
                       isIndirection : Boolean) : CCTerm =
    if (isIndirection)
      getPointedTerm(getPointerType(ind))
    else
      values(ind)

  private def getPointedTerm (ptrType : CCStackPointer) : CCTerm =
    ptrType.fieldAddress match {
      case Nil =>
        getValue(ptrType.targetInd, false)
      case _ =>
        val structVal = getValue(ptrType.targetInd, false)
        val structType = structVal.typ.asInstanceOf[CCStruct]
        structType.getFieldTerm(structVal, ptrType.fieldAddress)
    }

  private def setValue(name : String, t : CCTerm, enclosingFunction : String) : Unit =
    setValue(scope.lookupVar(name, enclosingFunction), t)
  private def setValue(ind: Int, t : CCTerm) : Unit = {
    val actualInd = getValue(ind, false).typ match {
      case stackPtr: CCStackPointer => stackPtr.targetInd
      case _ => ind
    }
    values = values.updated(actualInd, t)
    touchedGlobalState =
      touchedGlobalState || actualInd < scope.GlobalVars.size || !scope.freeFromGlobal(t)
  }

  private def getVar(ind: Int): CCVar = {
    if (ind < scope.GlobalVars.size) scope.GlobalVars.vars(ind)
    else scope.LocalVars.vars(ind - scope.GlobalVars.size)
  }
  private def getVar (name : String, enclosingFunction : String) : CCVar = {
    val ind = scope.lookupVar(name, enclosingFunction)
    getVar(ind)
  }

  def getValues : scala.Seq[CCTerm] =
    values.toList
  def getValuesAsTerms : scala.Seq[ITerm] =
    for (expr <- values.toList) yield expr.toTerm

  def asAtom(pred : CCPredicate) =
    context.atom(pred, getValuesAsTerms.take(pred.arity))

  def asLValue(exp : Exp) : String = exp match {
    case exp : EvarWithType => exp.cident_
    case exp : Evar    => exp.cident_
    case exp : Eselect => asLValue(exp.exp_)
    case exp : Epoint  => asLValue(exp.exp_)
    case exp : Epreop  => asLValue(exp.exp_)
    case exp : Eassign => asLValue(exp.exp_1)
    case exp : Earray  => asLValue(exp.exp_1)
    case exp =>
      throw new TranslationException(
        "Can only handle assignments to variables, not " +
        (context.printer print exp))
  }

  private def isClockVariable(exp : Exp, enclosingFunction : String)
  : Boolean = exp match {
    case exp : Evar => getValue(exp.cident_,
                                enclosingFunction).typ == CCClock
    case exp : EvarWithType => getValue(exp.cident_,
                                        enclosingFunction).typ == CCClock
    case _ : Eselect | _ : Epreop | _ : Epoint | _ : Earray => false
    case exp =>
      throw new TranslationException(getLineString(exp) +
                                     "Can only handle assignments to variables, not " +
                                     (context.printer print exp))
  }

  private def isDurationVariable(exp : Exp, enclosingFunction : String)
  : Boolean = exp match {
    case exp : Evar => getValue(exp.cident_,
                                enclosingFunction).typ == CCDuration
    case exp : EvarWithType => getValue(exp.cident_,
                                        enclosingFunction).typ == CCDuration
    case _ : Eselect | _ : Epreop | _ : Epoint | _ : Earray => false
    case exp =>
      throw new TranslationException(getLineString(exp) +
                                     "Can only handle assignments to variables, not " +
                                     (context.printer print exp))
  }

  private def isHeapPointer(t : CCTerm) =
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
                      evalCtx : EvalContext) : CCTerm = {
    val initSize = values.size
    evalHelp(exp)(evalSettings, evalCtx)
    val res = popVal
    assert(initSize == values.size)
    res
  }

  def evalList(exp : Exp) : scala.Seq[CCTerm] = {
    val res = new ArrayBuffer[CCTerm]

    var e = exp
    while (e.isInstanceOf[Ecomma]) {
      val ec = e.asInstanceOf[Ecomma]
      res += eval(ec.exp_2)(EvalSettings(), EvalContext())
      e = ec.exp_1
    }

    res += eval(e)(EvalSettings(), EvalContext())

    res.toList
  }

  def atomicEval(exp : Exp, evalCtx : EvalContext) : CCTerm =
    atomicEval(List(exp), evalCtx, Some(getSourceInfo(exp)))

  def atomicEval(exps : scala.Seq[Exp], evalCtx : EvalContext,
                 srcInfo : Option[SourceInfo]) : CCTerm = {
    val currentClauseNum = context.clausesSize
    val initSize = values.size

    context.inAtomicMode {
      pushVal(CCTerm.fromFormula(true, CCVoid, None))
      for (exp <- exps) {
        popVal
        evalHelp(exp)(EvalSettings(), evalCtx) // todo: EvalSettings(true)?
      }
    }

    if (currentClauseNum != context.clausesSize) {
      outputClause(srcInfo)
      context.mergeClauses(currentClauseNum)
    }
    val res = popVal
    assert(initSize == values.size)
    res
  }

  def atomicEvalFormula(exp : Exp, evalCtx : EvalContext) : CCTerm = {
    val initSize = values.size

    context.inAtomicMode{
      evalHelp(exp)(EvalSettings(), evalCtx)
    }

    val res = popVal
    assert(initSize == values.size)
    CCTerm.fromFormula(res.toFormula, res.typ, res.srcInfo)
  }

  // This function returns the actual term after an assignment is done.
  // E.g. for non ADT lhs, this is the same as the rhs,
  //      for ADT lhs, this is the lhs updated with the value of rhs.
  private def getActualAssignedTerm(lhs: CCTerm, rhs: CCTerm) = {
    if (rhs.typ.isInstanceOf[CCStruct] && (rhs.typ != lhs.typ))
      throw new TranslationException("Cannot assign " + rhs.typ +
                                     " to " + lhs.typ + "!")

    lhs.toTerm match {
      case fieldFun : IFunApp => // an ADT
        assignedToStruct = true
        val (fieldSelectors, rootTerm) = getFieldInfo(fieldFun)

        rootTerm match {
          case Left(t) =>
            val structType = context.structDefs(t.sort.name)
            val fieldAddress = structType.getFieldAddress(fieldSelectors)
            CCTerm.fromTerm(structType.setFieldTerm(t, rhs.toTerm, fieldAddress),
                   structType, rhs.srcInfo)
          case Right(f) =>
            val structType =
              context.structDefs(f.fun.asInstanceOf[MonoSortedIFunction].resSort.name)
            val fieldAddress = structType.getFieldAddress(fieldSelectors)
            CCTerm.fromTerm(structType.setFieldTerm(f, rhs.toTerm, fieldAddress),
                   structType, rhs.srcInfo)
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
          case nestedMore : IFunApp if !(context.objectGetters contains nestedMore.fun) =>
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

  def getStaticLocationId(srcInfo : SourceInfo) : CCTerm = {
    Symex.locationMap.getOrElseUpdate(srcInfo, {
      Symex.locationCounter += 1
      Symex.locationCounter
    })
    CCTerm.fromTerm(IIntLit(Symex.locationCounter), CCInt, Some(srcInfo))
  }

  private def getStaticLocationId(exp : Exp) : CCTerm =
    getStaticLocationId(getSourceInfo(exp))

  /**
   * Represents the target of an assignment operation. Each implementation
   * encapsulates the logic for writing a value to a specific kind of
   * program location (simple variable, struct field, etc.).
   * Examples:
   *  "s.f1.f2"  -> StructField(base="s", path=["f1", "f2"])
   *  "p->f"     -> StructField(base="p", path=["f"])
   *  "(*p).f"   -> StructField(base="p", path=["f"])
   *  "*p"       -> PointerDeref(base="p")
   *  "a[i]"     -> ArrayElement(base="a", index="i")
   *  "a[i].f"   -> ArrayStructField(base="a", index="i", path=["f"])
   */
  private sealed trait AssignmentTarget {
    /** The original sub-expression that this AssignmentTarget was created from. */
    def originalExp : Exp

    /** Performs the state update for this type of LHS. */
    def update(newValue : CCTerm)
              (implicit symex : Symex,
               evalSettings   : EvalSettings,
               evalCtx        : EvalContext) : Unit

    /** Same as update, but writes a non-deterministic value and also returns that value. */
    def updateNonDet(implicit symex : Symex,
                     evalSettings   : EvalSettings,
                     evalCtx        : EvalContext) : CCTerm = {
      val lhsVal = eval(originalExp)(evalSettings, evalCtx.withEvaluatingLHS(true))
      val nondetTerm = CCTerm.fromTerm(lhsVal.typ.getNonDet, lhsVal.typ, lhsVal.srcInfo)
      this.update(nondetTerm)
      nondetTerm
    }
  }

  private case class SimpleVar(exp : Exp) extends AssignmentTarget {
    override def originalExp : Exp = exp
    override def update(newValue : CCTerm)
                       (implicit symex : Symex,
                        evalSettings   : EvalSettings,
                        evalCtx        : EvalContext) : Unit = {
      val lhsVal = eval(exp)(evalSettings, evalCtx.withEvaluatingLHS(true))
      val lhsName = asLValue(exp)

      val actualRhsVal = newValue match {
        case CCTerm(_, _: CCStackPointer, srcInfo, _) =>
          throw new UnsupportedCFragmentException(
            getLineStringShort(srcInfo) + " Only limited support for stack pointers")
        case CCTerm(t@IIntLit(value), _, _, _) if isHeapPointer(lhsVal) =>
          if (value.intValue != 0) {
            throw new TranslationException("Pointer assignment only supports 0 (NULL)")
          } else {
            val rhsVal : ITerm = if(TriCeraParameters.get.invEncoding.isEmpty)
                                   context.heap.nullAddr()
                                 else t
            CCTerm.fromTerm(rhsVal, CCHeapPointer(context.heap, lhsVal.typ), newValue.srcInfo)
          }
        case _ => newValue
      }

      val actualLhsTerm = getActualAssignedTerm(lhsVal, actualRhsVal)

      newValue.typ match {
        case arrayPtr1 : CCHeapArrayPointer =>
          lhsVal.typ match {
            case _ : CCHeapPointer =>
              throw new TranslationException(
                getLineString(exp) + "Cannot assign an array value to " + lhsName)
            case arrayPtr2 : CCHeapArrayPointer if arrayPtr1 != arrayPtr2 =>
              if (arrayPtr1.arrayLocation == ArrayLocation.Stack &&
                  arrayPtr2.arrayLocation == ArrayLocation.Heap)
                scope.updateVarType(lhsName, arrayPtr1, evalCtx.enclosingFunctionName)
              else throw new UnsupportedCFragmentException(
                getLineString(exp) + "Pointer " + lhsName + " points to multiple array types.")
            case _ =>
          }
        case _ =>
      }
      setValue(lhsName, actualLhsTerm, evalCtx.enclosingFunctionName)
    }
  }

  private case class StructField(baseExp     : Exp,
                                 path        : List[String],
                                 originalExp : Exp) extends AssignmentTarget {
    override def update(newValue : CCTerm)
                       (implicit symex : Symex,
                        evalSettings   : EvalSettings,
                        evalCtx        : EvalContext) : Unit = {
      pushVal(newValue)
      val baseLHSVal = eval(baseExp)(evalSettings, evalCtx.withEvaluatingLHS(true))
      val newValue2 = popVal
      val locTerm = getStaticLocationId(originalExp)
      baseLHSVal.typ match {
        case ptr : CCHeapPointer => // p->f
          val structType = ptr.typ match {
            case st : CCStruct => st
            case sf : CCStructField => sf.structs(sf.structName)
            case _ => throw new TranslationException(
              "Pointer does not point to a struct type.")
          }

          val fieldAddress = getFieldAddress(structType, path)
          val fieldTerm = structType.getFieldTerm(baseLHSVal, fieldAddress)
          val actualRhsVal = newValue match { // must match on newValue, not newValue2
            case CCTerm(_, _: CCStackPointer, srcInfo, _) =>
              throw new UnsupportedCFragmentException(
                getLineStringShort(srcInfo) + " Only limited support for stack pointers")
            case CCTerm(IIntLit(value), _, _, _) if isHeapPointer(fieldTerm) =>
              if (value.intValue != 0) {
                throw new TranslationException("Pointer assignment only supports 0 (NULL)")
              } else CCTerm.fromTerm(
                context.heap.nullAddr(), CCHeapPointer(context.heap, fieldTerm.typ), newValue.srcInfo)
            case _ => newValue2
          }

          if (structType.sels.size > 1 || path.size > 1) {
            pushVal(baseLHSVal) // keep the address to be written in case we generate clauses
            pushVal(actualRhsVal)
            pushVal(processHeapResult(heapModel.read(baseLHSVal, values, locTerm)).get)
            maybeOutputClause(baseLHSVal.srcInfo)
            val oldStructTerm = popVal.toTerm // the result of the read
            val newValue3 = popVal     // the rhs value
            val curBaseLHSVal = popVal        // the address to write
            val newStructTerm = structType.setFieldTerm(oldStructTerm, newValue3.toTerm, fieldAddress)
            val newStructObj = wrapAsHeapObject(CCTerm.fromTerm(newStructTerm, structType, newValue3.srcInfo))
            processHeapResult(heapModel.write(curBaseLHSVal, newStructObj, values, locTerm))
          } else { // path.size == 1 && structType.sels.size == 1
            val newStructTerm = structType.setFieldTerm(actualRhsVal.toTerm)
            val newStructObj = wrapAsHeapObject(CCTerm.fromTerm(newStructTerm, structType, actualRhsVal.srcInfo))
            processHeapResult(heapModel.write(baseLHSVal, newStructObj, values, locTerm))
          }

        case structType : CCStruct => // s.f
          val varName = asLValue(baseExp)
          val fieldAddress = getFieldAddress(structType, path)
          val oldStructTerm = baseLHSVal.toTerm
          val newStructTerm = structType.setFieldTerm(oldStructTerm, newValue2.toTerm, fieldAddress)
          val newStructObj = CCTerm.fromTerm(newStructTerm, structType, newValue2.srcInfo)
          setValue(varName, newStructObj, evalCtx.enclosingFunctionName)
          assignedToStruct = true

        case _ : CCStackPointer => // ps->f
          pushVal(newValue2)
          val lhsVal = eval(originalExp)(evalSettings, evalCtx.withEvaluatingLHS(true))
          val newValue3 = popVal
          val lhsName = asLValue(originalExp)
          val actualLhsTerm = getActualAssignedTerm(lhsVal, newValue3)
          setValue(lhsName, actualLhsTerm, evalCtx.enclosingFunctionName)

        case _ => throw new TranslationException(
          "Invalid base for a struct field access: " + baseLHSVal)
      }
    }
  }

  private case class ArrayElement(arrayBase   : Exp,
                                  index       : Exp,
                                  originalExp : Exp) extends AssignmentTarget {
    override def update(newValue : CCTerm)
                       (implicit symex : Symex,
                        evalSettings   : EvalSettings,
                        evalCtx        : EvalContext): Unit = {
      val arrayTerm = eval(arrayBase)(evalSettings, evalCtx.withEvaluatingLHS(true))
      val indexTerm = eval(index)
      arrayTerm.typ match {
        case _ : CCHeapArrayPointer =>
          processHeapResult(heapModel.arrayWrite(
            arrayTerm, indexTerm, wrapAsHeapObject(newValue), values, getStaticLocationId(originalExp)))
        case _ : CCArray =>
          val lhsVal = eval(originalExp)(evalSettings, evalCtx.withEvaluatingLHS(true))
          val newTerm = CCTerm.fromTerm(writeADT(
            lhsVal.toTerm.asInstanceOf[IFunApp],
            newValue.toTerm, context.heap.userHeapConstructors,
            context.heap.userHeapSelectors), lhsVal.typ, newValue.srcInfo)
          val lhsName = asLValue(arrayBase)
          val oldLhsVal = getValue(lhsName, evalCtx.enclosingFunctionName)
          val innerTerm = lhsVal.toTerm.asInstanceOf[IFunApp].args.head
          val actualLhsTerm = getActualAssignedTerm(
            CCTerm.fromTerm(innerTerm, oldLhsVal.typ, newValue.srcInfo), newTerm)
          setValue(lhsName, actualLhsTerm, evalCtx.enclosingFunctionName)
        case _ => throw new TranslationException("Attempting array access on a non-array type.")
      }
    }
  }

  private case class ArrayStructField(arrayBase   : Exp,
                                      index       : Exp,
                                      path        : List[String],
                                      originalExp : Exp) extends AssignmentTarget {
    override def update(newValue : CCTerm)
                       (implicit symex : Symex,
                        evalSettings   : EvalSettings,
                        evalCtx        : EvalContext) : Unit = {
      val arrayTerm = eval(arrayBase)(evalSettings, evalCtx.withEvaluatingLHS(true))
      val indexTerm = eval(index)
      arrayTerm.typ match {
        case array : CCArray =>
          val oldStructTerm = array.arrayTheory.select(arrayTerm.toTerm, indexTerm.toTerm)
          val structType = array.elementType.asInstanceOf[CCStruct]
          val fieldAddress = getFieldAddress(structType, path)
          val newStructInnerTerm = structType.setFieldTerm(
            oldStructTerm, newValue.toTerm, fieldAddress)
          val newArrayTerm = array.arrayTheory.store(
            arrayTerm.toTerm, indexTerm.toTerm, newStructInnerTerm)
          val arrayVarName = asLValue(arrayBase)
          setValue(arrayVarName, CCTerm.fromTerm(
            newArrayTerm, arrayTerm.typ, newValue.srcInfo), evalCtx.enclosingFunctionName)

        case array : CCHeapArrayPointer =>
          val locTerm = getStaticLocationId(originalExp)
          val readResult = processHeapResult(heapModel.arrayRead(arrayTerm, indexTerm, values, locTerm)).get
          val oldStructTerm = readResult.toTerm
          val structType = array.elementType.asInstanceOf[CCStruct]
          val fieldAddress = getFieldAddress(structType, path)
          val newStructInnerTerm = structType.setFieldTerm(oldStructTerm, newValue.toTerm, fieldAddress)
          val newStructObj = CCTerm.fromTerm(newStructInnerTerm, structType, newValue.srcInfo)
          processHeapResult(heapModel.arrayWrite(
            arrayTerm, indexTerm, wrapAsHeapObject(newStructObj), values, locTerm))

        case _ => throw new TranslationException(
          "Field access on an element of a non-struct array.")
      }
    }
  }

  private case class PointerDeref(pointerExp  : Exp,
                                  originalExp : Exp) extends AssignmentTarget {
    override def update(newValue : CCTerm)
                       (implicit symex : Symex,
                        evalSettings   : EvalSettings,
                        evalCtx        : EvalContext) : Unit = {
      val pointerVal = eval(pointerExp)(evalSettings, evalCtx.withEvaluatingLHS(false))
      if (isHeapPointer(pointerVal)) {
        processHeapResult(heapModel.write(pointerVal, wrapAsHeapObject(newValue),
                                          values, getStaticLocationId(originalExp)))
      } else {
        val lhsVal = eval(originalExp)(evalSettings, evalCtx.withEvaluatingLHS(true))
        val lhsName = asLValue(originalExp)
        val actualLhsTerm = getActualAssignedTerm(lhsVal, newValue)
        setValue(lhsName, actualLhsTerm, evalCtx.enclosingFunctionName)
      }
    }
  }

  private def getAssignmentTarget(exp : Exp) : AssignmentTarget = exp match {
    case e: Earray =>
      ArrayElement(e.exp_1, e.exp_2, e)
    case e: Epoint =>
      StructField(e.exp_, List(e.cident_), e)
    case e: Eselect =>
      getAssignmentTarget(e.exp_) match {
        case StructField(base, path, _) => StructField(base, path :+ e.cident_, e)
        case SimpleVar(base)            => StructField(base, List(e.cident_), e)
        case PointerDeref(base, _)      => StructField(base, List(e.cident_), e)
        case ArrayElement(arrayBase, index, _) =>
          ArrayStructField(arrayBase, index, List(e.cident_), e)
        case ArrayStructField(arrayBase, index, path, _) =>
          ArrayStructField(arrayBase, index, path :+ e.cident_, e)
        case _ => throw new TranslationException(
          "Invalid expression for '.' member access in " + (context.printer print e))
      }
    case e: Epreop if e.unary_operator_.isInstanceOf[Indirection] =>
      PointerDeref(e.exp_, e)
    case e => SimpleVar(e)
  }

  /**
   * Converts a path of field names to a path of field indices based on the
   * struct type information.
   */
  private def getFieldAddress(structType : CCStruct, path : List[String]) : List[Int] = {
    if (path.isEmpty) return Nil

    val fieldName = path.head
    val fieldIndex = structType.getFieldIndex(fieldName)
    if (fieldIndex < 0)
      throw new TranslationException(
        s"Struct ${structType.shortName} has no field named '$fieldName'")

    val fieldType = structType.getFieldType(fieldIndex)

    if (path.tail.nonEmpty) fieldType match {
        case nestedType : CCStruct =>
          fieldIndex :: getFieldAddress(nestedType, path.tail)
        case CCStructField(name, structs) =>
          fieldIndex :: getFieldAddress(structs(name), path.tail)
        case _ =>
          throw new TranslationException(
            s"Trying to access field '${path.tail.head}' in a non-struct type")
    } else fieldIndex :: Nil
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

  private def heapModel : HeapModel = {
    maybeHeapModel match {
      case Some(heapModel) => heapModel
      case _ => throw NeedsHeapModelException
    }
  }

  private def wrapAsHeapObject(term : CCTerm) : CCTerm =
    context.sortWrapperMap get term.typ.toSort match {
      case Some(wrapper) =>
        CCTerm.fromTerm(wrapper(term.toTerm), CCHeapObject(context.heap), term.srcInfo)
      case None =>
        throw new TranslationException(
          s"No constructor found to make ${term.typ} a heap object!")
    }

  private def callFunction(name    : String,
                           args    : scala.Seq[CCTerm],
                           srcInfo : Option[SourceInfo]) : CCTerm = {
    args.foreach(pushVal(_))
    outputClause(srcInfo)
    handleFunction(name, initPred, args.size)
    calledFunction = true
    popVal
  }

  private def processHeapResult(result : HeapModel.HeapOperationResult)
  : Option[CCTerm] = result match {
    case HeapModel.SimpleResult(returnValue, newValues, assumptions, assertions) =>
      values = newValues
      assertions.foreach { case (f, p) =>
        assertProperty(f.toFormula, f.srcInfo, p) }
      // It is important that assumptions are added after assertions, otherwise
      // assertion guards will include the safety formula, which is unsound.
      assumptions.foreach(a => addGuard(a.toFormula))
      returnValue
    case call : HeapModel.FunctionCall =>
      Some(callFunction(call.functionName, call.args, call.sourceInfo))
    case call : HeapModel.FunctionCallWithGetter =>
      val callResult = callFunction(call.functionName, call.args, call.sourceInfo)
      val canAssumeMemorySafety = TriCeraParameters.get.invEncoding match {
        case Some(enc) => enc contains "-fun-"
        case None => false
      }
      if(canAssumeMemorySafety ||
         !context.propertiesToCheck.contains(properties.MemValidDeref)) {
        val safetyFormula = context.heap.hasUserHeapCtor(
          callResult.toTerm, context.sortCtorIdMap(call.resultType.toSort))
        addGuard(safetyFormula)
      }
      Some(CCTerm.fromTerm(call.getter(callResult.toTerm),
                  call.resultType,
                  call.sourceInfo))
  }

  def handleArrayInitialization(arrayPtr  : CCHeapArrayPointer,
                                arraySize : CCTerm,
                                initStack : mutable.Stack[ITerm],
                                locTerm   : CCTerm) : CCTerm = {
    val result =
      heapModel.allocAndInitArray(arrayPtr, arraySize.toTerm, initStack, values, locTerm)

    val returnValue = processHeapResult(result)

    returnValue.getOrElse(throw new TranslationException(
      "Array initialization did not return a pointer."))
  }

  def handleUninitializedArrayDecl(arrayTyp         : CCHeapArrayPointer,
                                   sizeExpr         : Option[Constant_expression],
                                   isGlobalOrStatic : Boolean,
                                   forceNondetInit  : Boolean) : CCTerm = {
    val sizeTerm = sizeExpr match {
      case Some(expr) =>
        Some(eval(expr.asInstanceOf[Especial].exp_)
             (EvalSettings(true), EvalContext()).toTerm)
      case None =>
        None
    }

    val result =
      heapModel.declUninitializedArray(arrayTyp, sizeTerm, isGlobalOrStatic, forceNondetInit, values)
    processHeapResult(result).getOrElse(
      throw new TranslationException(
        "Uninitialized array declaration did not return a pointer.")
    )
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
      setValue(asLValue(exp.exp_1), context.translateClockValue(topVal),
               evalCtx.enclosingFunctionName)
    case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign] &&
                           isDurationVariable(exp.exp_1,
                                              evalCtx.enclosingFunctionName)) =>
      evalHelp(exp.exp_2)
      maybeOutputClause(Some(getSourceInfo(exp)))
      setValue(asLValue(exp.exp_1), context.translateDurationValue(topVal),
               evalCtx.enclosingFunctionName)
    case exp : Eassign if exp.assignment_op_.isInstanceOf[Assign] => // Simple assignment: '='
      implicit val symex : Symex = this
      exp.exp_2 match {
        case _ : Enondet =>
          pushVal (getAssignmentTarget(exp.exp_1).updateNonDet)
        case _ =>
          evalHelp(exp.exp_2)
          maybeOutputClause(Some(getSourceInfo(exp)))
          getAssignmentTarget(exp.exp_1).update(topVal)
      }

    case exp : Eassign => // Compound assignment: '+=', '-=', etc.
      // IMPORTANT: Compound assignments are non-atomic so must be handled
      // separately from simple assignments.
      evalHelp(exp.exp_1)
      maybeOutputClause(Some(getSourceInfo(exp)))
      val lhsE = topVal
      val rhsE = exp.exp_2 match {
        case _ : Enondet => CCTerm.fromTerm(
          lhsE.typ.getNonDet, lhsE.typ, Some(getSourceInfo(exp.exp_2)))
        case _ =>
          evalHelp(exp.exp_2)
          maybeOutputClause(Some(getSourceInfo(exp)))
          popVal
      }
      popVal

      if (lhsE.typ == CCClock || lhsE.typ == CCDuration)
        throw new TranslationException("unsupported assignment to clock")

      val valueToAssign = CCTerm.fromTerm(
        lhsE.typ cast (exp.assignment_op_ match {
        case _ : AssignMul =>
          ap.theories.nia.GroebnerMultiplication.mult(lhsE.toTerm, rhsE.toTerm)
        case _ : AssignDiv =>
          ap.theories.nia.GroebnerMultiplication.tDiv(lhsE.toTerm, rhsE.toTerm)
        case _ : AssignMod =>
          ap.theories.nia.GroebnerMultiplication.tMod(lhsE.toTerm, rhsE.toTerm)
        case _ : AssignAdd =>
          (lhsE.typ, rhsE.typ) match {
            case (arrTyp : CCHeapArrayPointer, _ : CCArithType) =>
              // import arrTyp.heap._
              // nthAddrRange(addressRangeNth(lhsE.toTerm, rhsE.toTerm), addressRangeSize(lhsE.toTerm) - rhsE.toTerm)
              // TODO: this is unsafe, need to
              throw new UnsupportedCFragmentException(
                "Pointer arithmetic is currently not supported.")
            case _ => lhsE.toTerm + rhsE.toTerm
          }
        case _ : AssignSub =>
          (lhsE.typ, rhsE.typ) match {
            case (_ : CCHeapArrayPointer, _ : CCArithType) =>
              throw new TranslationException("Only addition is allowed in array pointer arithmetic.")
            case _ => lhsE.toTerm - rhsE.toTerm
          }
        case _ : AssignLeft =>
          ModuloArithmetic.bvshl(lhsE.typ cast2Unsigned lhsE.toTerm,
                                 lhsE.typ cast2Unsigned rhsE.toTerm)
        case _ : AssignRight =>
          ModuloArithmetic.bvashr(lhsE.typ cast2Unsigned lhsE.toTerm,
                                  lhsE.typ cast2Unsigned rhsE.toTerm)
        case _ : AssignAnd =>
          ModuloArithmetic.bvand(lhsE.typ cast2Unsigned lhsE.toTerm,
                                 lhsE.typ cast2Unsigned rhsE.toTerm)
        case _ : AssignXor =>
          ModuloArithmetic.bvxor(lhsE.typ cast2Unsigned lhsE.toTerm,
                                 lhsE.typ cast2Unsigned rhsE.toTerm)
        case _ : AssignOr =>
          ModuloArithmetic.bvor(lhsE.typ cast2Unsigned lhsE.toTerm,
                                lhsE.typ cast2Unsigned rhsE.toTerm)
      }), lhsE.typ, lhsE.srcInfo)

      pushVal(valueToAssign)
      implicit val symex: Symex = this
      getAssignmentTarget(exp.exp_1).update(valueToAssign)

    case exp : Econdition => // exp_1 ? exp_2 : exp_3
      val srcInfo = Some(getSourceInfo(exp))
      if(evalSettings.noClausesForExprs) {
        val oldSize = context.clausesSize
        val cond = eval(exp.exp_1)
        val t1 = eval(exp.exp_2)
        val t2 = eval(exp.exp_3)
        if(context.clausesSize > oldSize)
          throw new TranslationException("This ternary expression must be " +
                                         "side effect free: " +
                                         context.printer.print(exp) + " at line " +
                                         srcInfo.get.line)
        // throw exceptioon if t1.typ != t2.typ
        if(t1.typ != t2.typ)
          throw new TranslationException("Unsupported operation: ternary " +
                                         "expression with different types: " + context.printer.print(exp) +
                                         " at line " + srcInfo.get.line)
        pushVal(CCTerm.fromTerm(IExpression.ite(cond.toFormula, t1.toTerm, t2.toTerm),
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
        val lastLocalVar = scope.LocalVars.last
        scope.LocalVars.update(scope.LocalVars.size - 1,
                         new CCVar(s"ite_${srcInfo.get.line}_${srcInfo.get.col}",
                                   lastLocalVar.srcInfo, lastLocalVar.typ,
                                   lastLocalVar.storage))
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
        pushVal(CCTerm.fromFormula(cond ||| cond2, CCInt, srcInfo))
      } else {
        outputClause(srcInfo)
        val intermediatePred = initPred

        restoreState
        addGuard(cond)
        pushVal(CCTerm.fromFormula(
          true, intermediatePred.argVars.last.typ, srcInfo))
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
        pushVal(CCTerm.fromFormula(cond &&& cond2, CCInt, srcInfo))
      } else {
        outputClause(srcInfo)
        val intermediatePred = initPred

        restoreState
        addGuard(~cond)
        pushVal(CCTerm.fromFormula(
          false, intermediatePred.argVars.last.typ, srcInfo))
        outputClause(intermediatePred, srcInfo)
      }
    case exp : Ebitor =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.BitwiseOr(lhs, rhs).term)
    case exp : Ebitexor =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.BitwiseXor(lhs, rhs).term)
    case exp : Ebitand =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.BitwiseAnd(lhs, rhs).term)
    case exp : Eeq =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Equality(lhs, rhs).term)
    case exp : Eneq =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Disequality(lhs, rhs).term)
    case exp : Elthen =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Less(lhs, rhs).term)
    case exp : Egrthen =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Greater(lhs, rhs).term)
    case exp : Ele =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.LessEqual(lhs, rhs).term)
    case exp : Ege =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.GreaterEqual(lhs, rhs).term)
    case exp : Eleft =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.ShiftLeft(lhs, rhs).term)
    case exp : Eright =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.ShiftRight(lhs, rhs).term)
    case exp : Eplus =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Plus(lhs, rhs).term)
    case exp : Eminus =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Minus(lhs, rhs).term)
    case exp : Etimes =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Times(lhs, rhs).term)
    case exp : Ediv =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Div(lhs, rhs).term)
    case exp : Emod =>
      val (lhs, rhs) = evalBinExpArgs(exp.exp_1, exp.exp_2)
      pushVal(BinaryOperators.Mod(lhs, rhs).term)
    case exp : Etypeconv => {
      evalHelp(exp.exp_)
      pushVal(popVal convertToType context.getType(exp.type_name_))
    }
    case _ : Epreinc | _ : Epredec =>
      val (expToUpdate, op) = exp match {
        case e: Epreinc => (e.exp_, +1)
        case e: Epredec => (e.exp_, -1)
      }

      evalHelp(expToUpdate)
      maybeOutputClause(Some(getSourceInfo(exp)))
      val newValue = popVal mapTerm (_ + op)
      pushVal(newValue)
      implicit val symex: Symex = this
      getAssignmentTarget(expToUpdate).update(newValue)

    case _ : Epostinc | _ : Epostdec =>
      val (expToUpdate, op) = exp match {
        case e: Epostinc => (e.exp_, +1)
        case e: Epostdec => (e.exp_, -1)
      }

      evalHelp(expToUpdate)
      maybeOutputClause(Some(getSourceInfo(exp)))
      val newValue = topVal mapTerm (_ + op)
      implicit val symex: Symex = this
      getAssignmentTarget(expToUpdate).update(newValue)


    case exp : Epreop =>
      val srcInfo = Some(getSourceInfo(exp))
      evalHelp(exp.exp_)
      exp.unary_operator_ match {
        case _ : Address    =>
          topVal.toTerm match {
            case fieldFun: IFunApp
              if !(context.objectGetters contains fieldFun.fun) &&
                 (context.heap.userHeapSelectors exists(_ contains fieldFun.fun)) => // an ADT
              val (fieldNames, rootTerm) = getFieldInfo(fieldFun)
              rootTerm match {
                case Left(c) =>
                  val rootInd: Int = scope.lookupVar(c.name, evalCtx.enclosingFunctionName)
                  val structType = getValue(rootInd, false).typ.asInstanceOf[CCStruct]
                  assert(rootInd > -1 && rootInd < values.size - 1) // todo
                  val ptr = CCStackPointer(rootInd, popVal.typ, structType.getFieldAddress(fieldNames))
                  pushVal(CCTerm.fromTerm(IExpression.Int2ITerm(rootInd), ptr, srcInfo)) //we don't care about the value
                case Right(c) =>
                  throw new UnsupportedCFragmentException(
                    getLineStringShort(srcInfo) +
                    " Stack pointers in combination with heap pointers")
              }
            case f : IFunApp if context.objectGetters contains f.fun =>
              val readFunApp = f.args.head.asInstanceOf[IFunApp] // sth like read(h, ...)
              val scala.Seq(heapTerm, addrTerm) = readFunApp.args
              // todo: below type extraction is not safe!
              val heap = context.heap
              val t = addrTerm match {
                case IFunApp(heap.addressRangeNth, args) => // if nthAddrRange(a, i)
                  val scala.Seq(arrTerm, indTerm) = args
                  // return the addressRange starting from i
                  import heap._
                // TODO: implement this properly by adding an offset to pointers
//                  val newTerm = nthAddrRange(addressRangeNth(arrTerm, indTerm),
//                                             addressRangeSize(arrTerm) - indTerm)
//                  CCTerm.fromTerm(newTerm,
//                         getValue(arrTerm.asInstanceOf[IConstant].c.name,
//                                  evalCtx.enclosingFunctionName).typ, srcInfo)
                  throw new UnsupportedCFragmentException(
                    "There is currently limited support for arrays, " +
                    "we are working on it.")
                case _ =>
                  CCTerm.fromTerm(
                    addrTerm,
                    CCHeapPointer(context.heap,
                                  getValue(addrTerm.asInstanceOf[IConstant].c.name,
                                           evalCtx.enclosingFunctionName).typ), srcInfo)
              }
              popVal
              pushVal(t)

            case IFunApp(f@ExtArray.Select(arrTheory), scala.Seq(arrayTerm, indexTerm)) =>
              throw new UnsupportedCFragmentException(
                getLineString(srcInfo) +
                "Stack pointers to mathematical array fields are not yet supported."
              )

            case _ =>
              val t = if (evalCtx.handlingFunContractArgs) {
                throw new UnsupportedCFragmentException(
                  "Function contracts are currently not supported together " +
                  s"with stack pointers (${exp.line_num}:${exp.col_num})." +
                  s"(Recursive functions are encoded using contracts.)")
              } else {
                val ind = values.indexWhere(v => v == topVal)
                assert(ind > -1 && ind < values.size - 1) // todo
                val ptr = CCStackPointer(ind, popVal.typ, Nil)
                CCTerm.fromTerm(IExpression.Int2ITerm(ind), ptr, srcInfo)
              }
              pushVal(t) //we don't care about the value
          }
        case _ : Indirection =>
          val v = popVal
          v.typ match { // todo: type checking?
            case ptr : CCStackPointer => pushVal(getPointedTerm(ptr))
            case   _ : CCHeapPointer =>
              if(evalCtx.evaluatingLHS) pushVal(v)
              else pushVal(processHeapResult(heapModel.read(v, values, getStaticLocationId(exp))).get)
            case  arr : CCHeapArrayPointer =>
              if(evalCtx.evaluatingLHS) pushVal(v)
              else pushVal(processHeapResult(heapModel.arrayRead(
                v, CCTerm.fromTerm(IIntLit(0), CCInt, srcInfo), values, getStaticLocationId(exp))).get)
            case _ => throw new TranslationException(
              "Cannot dereference non-pointer: " + v.typ + " " + v.toTerm)
          }
        case _ : Plus       => // nothing
        case _ : Negative   =>
          val t = popVal mapTerm (-(_))
          pushVal(CCTerm.fromTerm(t.toTerm, t.typ, srcInfo))
//          case _ : Complement.  Unary_operator ::= "~" ;
        case _ : Logicalneg =>
          pushVal(CCTerm.fromFormula(~popVal.toFormula, CCInt, srcInfo))
      }
    case exp : Ebytesexpr => // Exp15 ::= "sizeof" Exp15;
      val srcInfo = Some(getSourceInfo(exp))
      val inner = eval(exp.exp_)
      pushVal(CCTerm.fromTerm(IdealInt(inner.typ.sizeInBytes), CCUInt, srcInfo))
    case exp : Ebytestype => //  Exp15 ::= "sizeof" "(" Type_name ")";
      val srcInfo = Some(getSourceInfo(exp))
      val typ = context.getType(exp)
      pushVal(CCTerm.fromTerm(IdealInt(typ.sizeInBytes), CCUInt, srcInfo))

//    case exp : Earray.      Exp16 ::= Exp16 "[" Exp "]" ;

    case exp : Efunk =>
      val srcInfo = Some(getSourceInfo(exp))
      // inline the called function
      GetId.orString(exp) match {
        case "reach_error" =>
          /**
           * A special SV-COMP function used in the unreach-call category.
           * We directly rewrite this as `assert(0)` when checking reach safety..
           */
          if(context.propertiesToCheck contains properties.Reachability)
            assertProperty(false, srcInfo, properties.Reachability)
          pushVal(CCTerm.fromFormula(true, CCInt, srcInfo))
        case "abort" =>
          /** Treat abort as assert(0). */
          assertProperty(false, srcInfo, properties.UserAssertion)
          pushVal(CCTerm.fromFormula(true, CCInt, srcInfo))
        case "$HEAP_TYPE_DEFAULT" =>
          /** A builtin to access the default object of the heap */
          pushVal(CCTerm.fromTerm(context.heap.defaultObject,
                                  CCHeapObject(context.heap), srcInfo))
        case name =>
          outputClause(srcInfo)
          handleFunction(name, initPred, 0)
      }

    case exp : Efunkpar =>
      val srcInfo = Some(getSourceInfo(exp))
      GetId.orString(exp) match {
        case "assert" | "static_assert" if exp.listexp_.size == 1 =>
          val property = exp.listexp_.asScala.head match {
            case a : Efunkpar
              if context.uninterpPredDecls contains(GetId.orString(a)) =>
              val args = a.listexp_.asScala.map(exp => atomicEval(exp, evalCtx))
              if(args.exists(a => a.typ.isInstanceOf[CCStackPointer])) {
                throw new TranslationException(
                  getLineStringShort(srcInfo) + " Unsupported operation: " +
                  "stack pointer argument to uninterpreted predicate.")
              }
              val pred = context.uninterpPredDecls(GetId.orString(a))
              context.atom(pred, args.map(_.toTerm).toSeq)
            case interpPred : Efunkpar
              if context.interpPredDefs contains(GetId.orString(interpPred)) =>
              val args    = interpPred.listexp_.asScala.map(
                exp => atomicEval(exp, evalCtx)).map(_.toTerm)
              val formula = context.interpPredDefs(GetId.orString(interpPred))
              // the formula refers to pred arguments as IVariable(index)
              // we need to subsitute those for the actual arguments
              VariableSubstVisitor(formula.toFormula, (args.toList, 0))
            case _ =>
              atomicEvalFormula(exp.listexp_. asScala.head, evalCtx).toFormula
          }
          assertProperty(property, srcInfo, properties.UserAssertion)
          pushVal(CCTerm.fromFormula(true, CCInt, srcInfo))
        case "exit" if exp.listexp_.size == 1 =>
          addGuard(IBoolLit(false))
          pushVal(CCTerm.fromFormula(false, CCInt, srcInfo))
        case "assume" if exp.listexp_.size == 1 =>
          val property = exp.listexp_.asScala.head match {
            case a : Efunkpar
              if context.uninterpPredDecls contains(GetId.orString(a)) =>
              val args = a.listexp_.asScala.map(exp => atomicEval(exp, evalCtx))
                          .map(_.toTerm).toSeq
              val pred = context.uninterpPredDecls(GetId.orString(a))
              context.atom(pred, args)
            case interpPred : Efunkpar
              if context.interpPredDefs contains (GetId.orString(interpPred)) =>
              val args = interpPred.listexp_.asScala.map(
                exp => atomicEval(exp, evalCtx)).map(_.toTerm)
              val formula = context.interpPredDefs(GetId.orString(interpPred))
              // the formula refers to pred arguments as IVariable(index)
              // we need to subsitute those for the actual arguments
              VariableSubstVisitor(formula.toFormula, (args.toList, 0))
            case _ =>
              atomicEvalFormula(exp.listexp_.asScala.head, evalCtx).toFormula
          }
          addGuard(property)
          pushVal(CCTerm.fromFormula(true, CCInt, srcInfo))
        case cmd@("chan_send" | "chan_receive") if (exp.listexp_.size == 1) =>
          val name = GetId.orString(exp.listexp_.asScala.head)
          (context.channels get name) match {
            case Some(chan) => {
              val sync = cmd match {
                case "chan_send"    => ParametricEncoder.Send(chan)
                case "chan_receive" => ParametricEncoder.Receive(chan)
              }
              outputClause(context.newPred(Nil, srcInfo), srcInfo, sync)
              pushVal(CCTerm.fromFormula(true, CCInt, srcInfo))
            }
            case None =>
              throw new TranslationException(
                name + " is not a declared channel")
          }
        case name@("malloc" | "calloc" | "alloca" | "__builtin_alloca")
          if !TriCeraParameters.get.useArraysForHeap => // todo: proper alloca and calloc
          val (typ, allocSize) = exp.listexp_.asScala(0) match {
            case exp : Ebytestype =>
              (context.getType(exp), CCTerm.fromTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))
            //case exp : Ebytesexpr => eval(exp.exp_).typ - handled by preprocessor
            case exp : Etimes =>
              exp.exp_1 match {
                case e : Ebytestype => (context.getType(e), eval(exp.exp_2))
                case e if exp.exp_2.isInstanceOf[Ebytestype] =>
                  (context.getType(exp.exp_2.asInstanceOf[Ebytestype]), eval(e))
                case _ =>
                  throw new UnsupportedCFragmentException(
                    getLineStringShort(srcInfo) +
                    " Unsupported alloc expression: " + (context.printer print exp))
              }
            //case exp : Evar => // allocation in bytes
            case e : Econst => // allocation in bytes
              (CCInt, eval(e)) // todo: add support for char?

            case _ => throw new UnsupportedCFragmentException(
              getLineStringShort(srcInfo) +
              " Unsupported alloc expression: " + (context.printer print exp))
          }

          val arrayLoc = name match {
            case "malloc" | "calloc"           => ArrayLocation.Heap
            case "alloca" | "__builtin_alloca" => ArrayLocation.Stack
          }

          val canAssumeMemorySafety = TriCeraParameters.get.invEncoding match {
            case Some(enc) => enc contains "-fun-"
            case None => false
          }

          val objectTerm = CCTerm.fromTerm(name match {
                                    case "calloc"                                 => typ.getZeroInit
                                    case _ if canAssumeMemorySafety               => typ.getZeroInit
                                    case "malloc" | "alloca" | "__builtin_alloca" => typ.getNonDet
                                  }, typ, srcInfo)

          allocSize match {
            case CCTerm(IIntLit(IdealInt(1)), typ, _, _)
              if typ.isInstanceOf[CCArithType] && !evalCtx.lhsIsArrayPointer
                 && arrayLoc == ArrayLocation.Heap =>
              /**
               * global and stack arrays are allocated using CCHeapArrayPointer,
               * because CCHeapPointer does not distinguish between different
               * allocation types. This difference is needed for correctly
               * checking memory properties (e.g., only heap allocated memory
               * can be freed).
               */

              val allocatedAddr = processHeapResult(
                heapModel.alloc(wrapAsHeapObject(objectTerm), objectTerm.typ, values, getStaticLocationId(exp))).get

              pushVal(allocatedAddr)
            case CCTerm(sizeExp, typ, _, _) if typ.isInstanceOf[CCArithType] =>
              val addressRangeValue =
                processHeapResult(
                  heapModel.batchAlloc(objectTerm, sizeExp, arrayLoc, values)).get

              pushVal(addressRangeValue)
            // case CCTerm.fromTerm(IIntLit(IdealInt(n)), CCInt) =>
            // todo: optimise constant size allocations > 1?
          }
        case name@("malloc" | "calloc" | "alloca" | "__builtin_alloca")
          if TriCeraParameters.get.useArraysForHeap =>
          /**
           * @todo Support checking [[properties.MemValidCleanup]] when using
           *       arrays to model heaps.
           */

          val (typ, allocSize) = exp.listexp_.asScala(0) match {
            case exp : Ebytestype =>
              (context.getType(exp), CCTerm.fromTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))
            //case exp : Ebytesexpr => eval(exp.exp_).typ - handled by preprocessor
            case exp : Etimes =>
              exp.exp_1 match {
                case e : Ebytestype => (context.getType(e), eval(exp.exp_2))
                case e if exp.exp_2.isInstanceOf[Ebytestype] =>
                  (context.getType(exp.exp_2.asInstanceOf[Ebytestype]), eval(e))
                case _ =>
                  throw new UnsupportedCFragmentException(
                    "Unsupported alloc expression: " + (context.printer print exp))
              }
            //case exp : Evar => // allocation in bytes

            case _ => throw new UnsupportedCFragmentException(
              "Unsupported alloc expression: " + (context.printer print exp))
          }

          val (sizeExpr, sizeInt) = allocSize match {
            case CCTerm(IIntLit(IdealInt(n)), typ, _, _)
              if typ.isInstanceOf[CCArithType] && !evalCtx.lhsIsArrayPointer =>
              (Some(allocSize), Some(n))
            case _ =>
              (Some(allocSize), None)
          }

          sizeInt match {
            case Some(1) =>
            // use regular heap model, this is not an array
              val canAssumeMemorySafety = TriCeraParameters.get.invEncoding match {
                case Some(enc) => enc contains "-fun-"
                case None => false
              }

              val objectTerm = CCTerm.fromTerm(name match {
                case "calloc"                                 => typ.getZeroInit
                case _ if canAssumeMemorySafety               => typ.getZeroInit
                case "malloc" | "alloca" | "__builtin_alloca" => typ.getNonDet
              }, typ, srcInfo)

              val allocatedAddr = processHeapResult(
                heapModel.alloc(wrapAsHeapObject(objectTerm), objectTerm.typ, values, getStaticLocationId(exp))).get

              pushVal(allocatedAddr)
            case _ =>
              val arrayLocation = name match {
                case "malloc" | "calloc"           => ArrayLocation.Heap
                case "alloca" | "__builtin_alloca" => ArrayLocation.Stack
              }

              val theory = ExtArray(scala.Seq(CCInt.toSort), typ.toSort) // todo: only 1-d int arrays...
              val arrType = CCArray(typ, sizeExpr, sizeInt, theory, arrayLocation)

              val arrayTerm = CCTerm.fromTerm(name match {
                case "calloc"                                 => arrType.getZeroInit
                case "malloc" | "alloca" | "__builtin_alloca" => arrType.getNonDet
              }, arrType, srcInfo)

              pushVal(arrayTerm)
          }

        case "realloc" =>
          throw new TranslationException("realloc is not supported.")
        case "free" =>
          val ptrExpr = atomicEval(exp.listexp_.asScala.head, evalCtx)
          processHeapResult(heapModel.free(ptrExpr, values, getStaticLocationId(exp)))
          pushVal(CCTerm.fromTerm(0, CCVoid, srcInfo)) // free returns no value, push dummy
        case name =>
          // then we inline the called function

          // evaluate the arguments
          // todo: if we are to handle a function contract, arguments are handled
          // as heap pointers. if the function is to be inlined, then arguments
          // are handled as stack pointers. here we set a flag to notify this
          val handlingFunctionContractArgs = context.functionContexts.contains(name)
          val newEvalCtx = evalCtx
            .withHandlingFunContractArgs(handlingFunctionContractArgs)
            .incrementCallDepth
          for (e <- exp.listexp_.asScala)
            evalHelp(e)(evalSettings, newEvalCtx.withFunctionName(name))

          // substitute fresh variable names (e.g., __eval) with actual function argument names
          val argCount = exp.listexp_.size
          val argNames = context.functionDefs get name match {
            case Some(f) => context.getFunctionArgNames(f)
            case None =>
              context.uninterpPredDecls get name match {
                case Some(predDecl) =>
                  predDecl.argVars.map(_.name)
                case None => Nil
              }
          }
          if(argNames.nonEmpty) {
            val evalVars = scope.LocalVars.getVarsInTopFrame.takeRight(argCount)
            scope.LocalVars.pop(argCount) // remove those vars
            assert(argNames.length == argCount && evalVars.length == argCount)
            val newVars = if (evalVars.exists(v => context.isTermUsedInClauses(v.term))) {
              // todo: replace terms by substituting them if they were added to clauses too!
              evalVars
            } else {
              for ((oldVar, argName) <- evalVars zip argNames) yield {
                val uniqueArgName = name + "`" + argName
                new CCVar(uniqueArgName, oldVar.srcInfo, oldVar.typ,
                          oldVar.storage)
              }
            }
            newVars.foreach(v => scope.LocalVars.addVar(v))
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
      val subexpr = eval(exp.exp_)
      val rawFieldName = exp.cident_
      subexpr.typ match {
        case structType : CCStruct => // todo a better way
          if(!structType.contains(rawFieldName))
            throw new TranslationException(rawFieldName + " is not a member of "
                                           + structType + "!")
          val ind = structType.getFieldIndex(rawFieldName)
          val fieldType = structType.getFieldType(ind)
          val sel = structType.getADTSelector(ind)
          pushVal(CCTerm.fromTerm(sel(subexpr.toTerm), fieldType, srcInfo))
        case _ =>
          throw new TranslationException("Trying to access field '." +
                                         rawFieldName + "' of a variable which is not a struct.")
      }

    case exp : Epoint =>
      val srcInfo = Some(getSourceInfo(exp))
      val subexpr = eval(exp.exp_)
      val rawFieldName = exp.cident_
      val term = subexpr.typ match {
        case ptrType : CCStackPointer => getPointedTerm(ptrType)
        case _ : CCHeapPointer =>  //todo: error here if field is null
          processHeapResult(heapModel.read(subexpr, values, getStaticLocationId(exp))).get
        case _ => throw new TranslationException(
          "Trying to access field '->" + rawFieldName + "' of non pointer.")
      }
      val structType = term.typ match {
        case typ : CCStruct => typ
        case CCStructField(name, structs) => structs(name)
        case typ => throw new TranslationException("Epoint is currently " +
                                                   "only implemented for structs, not " + typ + ": " +
                                                   (context.printer print exp))
      }
      if(!structType.contains(rawFieldName))
        throw new TranslationException(rawFieldName + " is not a member of "
                                       + structType + "!")
      val ind = structType.getFieldIndex(rawFieldName)
      val fieldType = structType.getFieldType(ind)
      val sel = structType.getADTSelector(ind)
      pushVal(CCTerm.fromTerm(sel(term.toTerm), fieldType, srcInfo))

    case exp : Evar =>
      // todo: Unify with EvarWithType, they should always be treated the same.
      val name = exp.cident_
      name match {
        // TODO: FIX!!
        case "HEAP_TYPE_DEFAULT" =>
          pushVal(CCTerm.fromTerm(context.heap.defaultObject,
                                  CCHeapObject(context.heap), Some(getSourceInfo(exp))))
        case _ =>
          pushVal(scope.lookupVarNoException(name, evalCtx.enclosingFunctionName) match {
                    case -1 =>
                      (context.enumeratorDefs get name) match {
                        case Some(e) => e
                        case None => throw new TranslationException(
                          getLineString(exp) + "Symbol " + name + " is not declared")
                      }
                    case ind =>
                      getValue(ind, false)
                  })
      }


    case exp : EvarWithType =>
      // todo: Unify with Evar, they should always be treated the same.
      val name = exp.cident_
      pushVal(scope.lookupVarNoException(name, evalCtx.enclosingFunctionName) match {
                case -1 =>
                  (context.enumeratorDefs get name) match {
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
      pushVal(CCTerm.fromTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))

    case exp : Earray =>
      val srcInfo = Some(getSourceInfo(exp))
      val arrayTerm : CCTerm = eval(exp.exp_1)
      val index : CCTerm = eval(exp.exp_2)

      import IExpression._
      arrayTerm.typ match {
        case _ : CCHeapArrayPointer =>
          pushVal(processHeapResult(heapModel.arrayRead(
            arrayTerm, index, values, getStaticLocationId(exp))).get)
        case array : CCArray => // todo: move to separate method
          val readValue = CCTerm.fromTerm(
            array.arrayTheory.select(arrayTerm.toTerm, index.toTerm),
            array.elementType, srcInfo)
          array.sizeExpr match {
            case Some(expr)
              if context.propertiesToCheck contains properties.MemValidDeref =>
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

    // Only one very specific statement expression is support for now:
    // ((void) sizeof(int), ({ if (guard) ; /* empty */ else __assert_fail (...); }));
    // This is used as a macro to implement "assert" in "assert.h", so we reduce it to that.
    case exp : Estmexp =>
      def throwUnsupportedFragment = throw new UnsupportedCFragmentException(
        getLineString(exp) + "Only limited support for statement expressions")
      exp.compound_stm_ match {
        case _ : ScompOne => throw new TranslationException(
          getLineString(exp) + "Empty statement expression.")
        case comp : ScompTwo if comp.liststm_.size() == 1 &&
                          comp.liststm_.asScala.head.isInstanceOf[SelS] =>
          comp.liststm_.asScala.head.asInstanceOf[SelS].selection_stm_ match {
            case ssel : SselTwo if ssel.stm_1.isInstanceOf[ExprS] &&
                                   ssel.stm_2.isInstanceOf[ExprS] =>
              if (!ssel.stm_1.asInstanceOf[ExprS].expression_stm_
                       .isInstanceOf[SexprOne] || // first part is not an empty stm or
                  !ssel.stm_2.asInstanceOf[ExprS].expression_stm_
                       .isInstanceOf[SexprTwo])   // second part is an empty stm
                throwUnsupportedFragment
              val lastExp = ssel.stm_2.asInstanceOf[ExprS].expression_stm_
                                .asInstanceOf[SexprTwo].exp_
              lastExp match {
                case funExp : Efunkpar =>
                  val funName = asLValue(funExp.exp_)
                  funName match {
                    case "__assert_fail" =>
                      // transform the whole thing to an assert statement
                      val assertArgList = new ListExp()
                      assertArgList.add(ssel.exp_) // add the guard as arg
                      evalHelp(new Efunkpar(new Evar("assert"), assertArgList))
                    case _ => throwUnsupportedFragment
                  }
                case _ => throwUnsupportedFragment
              }
            case _ => throwUnsupportedFragment
          }
        case _ => throwUnsupportedFragment
      }

    case _ =>
      throw new TranslationException(getLineString(exp) +
                                     "Expression currently not supported by TriCera: " +
                                     (context.printer print exp))
  }

  private def handleFunction(name : String,
                             functionEntry : CCPredicate,
                             argCount : Int) =
    context.functionContexts get name match {
      case Some(ctx) =>
        // use the contract of the function
//          assert(!(pointerArgs exists (_.isInstanceOf[CCStackPointer])),
//                 "function contracts do not support pointer arguments yet")

        val funDef = context.functionDefs(name)

        var argTerms : List[ITerm] = List()
        for (_ <- 0 until argCount)
          argTerms = popVal.toTerm :: argTerms

        val postGlobalVars : scala.Seq[ITerm] = // todo : use ctx postglobal?
          (for (v <- scope.GlobalVars.vars) yield {
            if (v.isStatic) {
              throw new TranslationException(
                "Static variables with contracts are not supported yet.")
              // todo: this should be easy to support, need to distinguish
              //       at a few locations the static variables belonging to
              //       that function only.
            }
            IExpression.i(v.sort newConstant(v.name + Literals.postExecSuffix)) //
            // todo: refactor
          }).toSeq

        val globals : scala.Seq[ITerm] =
          for (n <- 0 until scope.GlobalVars.size)
            yield getValue(n, false).toTerm

        val prePredArgs : scala.Seq[ITerm] = globals ++ argTerms

        val resVar : scala.Seq[CCVar] = scope.getResVar(context.getType(funDef))
        val postPredArgs : scala.Seq[ITerm] =
          prePredArgs ++ postGlobalVars ++ resVar.map(c => IConstant(c.term))

        val preAtom  = ctx.prePred(prePredArgs)
        val postAtom = ctx.postPred(postPredArgs)

        assertProperty(preAtom, functionEntry.srcInfo,
                       properties.FunctionPrecondition(name,functionEntry.srcInfo))

        addGuard(postAtom)

        for (((c, t), n) <- (postGlobalVars.iterator zip
                             scope.GlobalVars.formalTypes.iterator).zipWithIndex)
          setValue(n, CCTerm.fromTerm(c, t, None)) // todo: srcInfo?

        resVar match {
          case scala.Seq(v) => pushVal(CCTerm.fromTerm(v.term, v.typ, v.srcInfo))
          case scala.Seq()  => pushVal(CCTerm.fromTerm(0, CCVoid, None)) // push a dummy result
        }
      case None =>
        context.uninterpPredDecls get name match {
          case Some(predDecl) =>
            var argTerms : List[ITerm] = List()
            for (_ <- 0 until argCount) {
              argTerms = popVal.toTerm :: argTerms
            }
            pushVal(CCTerm.fromFormula(predDecl(argTerms), CCInt, None)) // todo:srcInfo
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
    context.functionDefs get name match {
      case Some(fundef) =>
        val typ = context.getType(fundef)
        val isNoReturn = typ == CCVoid
        val exitVar =
          if (isNoReturn) Nil
          else List(new CCVar("_" + name + "Ret", None, typ, AutoStorage)) // todo: return line no?
        val srcInfo = Some(FuncDef(fundef).sourceInfo)
        val functionExit = context.newPred(exitVar, srcInfo) // todo: return line no?

        context.inlineFunction(fundef, functionEntry, functionExit, pointerArgs,
                               isNoReturn, name)

        // reserve an argument for the function result

        if (typ == CCVoid)
          pushFormalVal(CCInt, srcInfo)
        else
          pushFormalVal(typ, srcInfo)
        resetFields(functionExit)
      case None => (context.functionDecls get name) match {
        case Some((fundecl, typ)) =>
          if (!name.contains("__VERIFIER_nondet") &&
              !context.warnedFunctionNames.contains(name)) {
            warn("no definition of function \"" + name + "\" available")
            context.warnedFunctionNames += name
          }
          pushFormalVal(typ, Some(getSourceInfo(fundecl)))
        case None =>
          throw new TranslationException(
            "Function " + name + " is not declared")
      }
    }

  private def checkPointerIntComparison(t1 : CCTerm, t2 : CCTerm) :
  (CCTerm, CCTerm) = {
    (t1.typ, t2.typ) match {
      case (_ : CCHeapPointer, _ : CCArithType) =>
        if (t2.toTerm != IIntLit(IdealInt(0)))
          throw new TranslationException("Pointers can only compared with `null` or `0`. " +
                                         getLineString(t2.srcInfo))
        else {
          val actualT2 = if(TriCeraParameters.get.invEncoding.isEmpty)
                           context.heap.nullAddr()
                         else t2.toTerm
          (t1, CCTerm.fromTerm(actualT2, t1.typ, t1.srcInfo)) // 0 to nullAddr()
        }
      case (_: CCArithType, _: CCHeapPointer) =>
        if (t1.toTerm != IIntLit(IdealInt(0)))
          throw new TranslationException("Pointers can only compared with `null` or `0`. " +
                                         getLineString(t2.srcInfo))
        else {
          val actualT1 = if(TriCeraParameters.get.invEncoding.isEmpty)
                           context.heap.nullAddr()
                         else t1.toTerm
          (CCTerm.fromTerm(actualT1, t2.typ, t2.srcInfo), t2) // 0 to nullAddr()
        }
      case _ => (t1, t2)
    }
  }

  private def evalBinExpArgs(left : Exp, right : Exp)
                            (implicit evalSettings : EvalSettings,
                             evalContext  : EvalContext) :
  (CCTerm, CCTerm) = {
    val (lhs, rhs) =
      if (evalSettings.noClausesForExprs) {
        (eval(left), eval(right))
      } else {
        // Do not push/pop lhs if it is a simple constant.
        val maybeLHS = eval(left) match {
          case lhs@CCTerm(IIntLit(v), _, _, _) => Some(lhs)
          case lhs =>
            pushVal(lhs)
            None
        }
        maybeOutputClause(Some(getSourceInfo(left)))
        evalHelp(right)
        val rhs = popVal
        val lhs = maybeLHS match {
          case Some(lhs) => lhs
          case None => popVal
        }
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
        pushVal(CCTerm.fromTerm(IdealInt(constant.char_.toInt), CCInt, srcInfo))
      case constant : Eunsigned =>
        pushVal(CCTerm.fromTerm(IdealInt(
          constant.unsigned_.substring(
            0, constant.unsigned_.size - 1)), CCUInt, srcInfo))
      case constant : Elong =>
        pushVal(CCTerm.fromTerm(IdealInt(
          constant.long_.substring(
            0, constant.long_.size - 1)), CCLong, srcInfo))
      case constant : Eunsignlong =>
        pushVal(CCTerm.fromTerm(IdealInt(
          constant.unsignedlong_.substring(
            0, constant.unsignedlong_.size - 2)), CCULong, srcInfo))
      case constant : Ehexadec =>
        pushVal(CCTerm.fromTerm(IdealInt(
          constant.hexadecimal_ substring 2, 16), CCInt, srcInfo))
      case constant : Ehexaunsign =>
        pushVal(CCTerm.fromTerm(IdealInt(constant.hexunsigned_.substring(
          2, constant.hexunsigned_.size - 1), 16), CCUInt, srcInfo))
      case constant : Ehexalong =>
        pushVal(CCTerm.fromTerm(IdealInt(constant.hexlong_.substring(
          2, constant.hexlong_.size - 1), 16), CCLong, srcInfo))
      case constant : Ehexaunslong =>
        pushVal(CCTerm.fromTerm(IdealInt(constant.hexunslong_.substring(
          2, constant.hexunslong_.size - 2), 16), CCULong, srcInfo))
      case constant : Eoctal =>
        pushVal(CCTerm.fromTerm(IdealInt(constant.octal_, 8), CCInt, srcInfo))
//      case constant : Eoctalunsign.  Constant ::= OctalUnsigned;
      case constant : Eoctallong =>
        pushVal(CCTerm.fromTerm(IdealInt(constant.octallong_.substring(
          0, constant.octallong_.size - 1), 8), CCLong, srcInfo))
//      case constant : Eoctalunslong. Constant ::= OctalUnsLong;
//      case constant : Ecdouble.      Constant ::= CDouble;
//      case constant : Ecfloat.       Constant ::= CFloat;
//      case constant : Eclongdouble.  Constant ::= CLongDouble;
      case constant : Eint =>
        pushVal(CCTerm.fromTerm(IExpression.i(IdealInt(
          constant.unboundedinteger_)), CCInt, srcInfo))
      case constant => throw new TranslationException(
        "Unimplemented type: " + constant.getClass)
    }
  }
}
