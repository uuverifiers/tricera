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

import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}
import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, Stack}

object Symex {
  def apply(context        : SymexContext,
            scope          : CCScope,
            initPred       : CCPredicate,
            maybeHeapModel : Option[HeapModel]) : Symex = {
    new Symex(context, scope, initPred, maybeHeapModel)
  }
}

class Symex private (context        : SymexContext,
                     scope          : CCScope,
                     oriInitPred    : CCPredicate,
                     maybeHeapModel : Option[HeapModel]) {
  private var values : Seq[CCExpr] =
    scope.allFormalVars.map(v => CCTerm(v.term, v.typ, v.srcInfo))
  private var guard : IFormula = true
  private var touchedGlobalState : Boolean = false
  private var assignedToStruct : Boolean = false

  private implicit def toRichExpr(expr : CCExpr) :
  Object{def mapTerm(m:ITerm => ITerm) : CCExpr} = new Object {
    def mapTerm(m : ITerm => ITerm) : CCExpr =
      // TODO: type promotion when needed
      CCTerm(expr.typ cast m(expr.toTerm), expr.typ, expr.srcInfo)
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

  private val savedStates = new Stack[(IAtom, Seq[CCExpr], IFormula, /*IFormula,*/ Boolean)]
  def saveState =
    savedStates push ((initAtom, values.toList, guard, touchedGlobalState))
  def restoreState = {
    val (oldAtom, oldValues, oldGuard, /*oldPullGuard,*/ oldTouched) = savedStates.pop
    initAtom = oldAtom
    values = oldValues
    scope.LocalVars.pop(scope.LocalVars.size - values.size + scope.GlobalVars.size)
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

  private def maybeOutputClause(srcInfo : Option[SourceInfo]) : Unit =
    if (((!context.atomicMode && touchedGlobalState) || assignedToStruct))
      outputClause(srcInfo)

  private def pushVal(v : CCExpr, varName : String = "") = {
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
                               varMapping mapValues (IExpression.v(_)))
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
    addValue(CCTerm(freshVar.term, typ, srcInfo))
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
    for ((e, i) <- scope.allFormalExprs.iterator.zipWithIndex) {
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

  def addValue(t : CCExpr) = {
    values = values ++ Seq(t)
    touchedGlobalState = touchedGlobalState || !scope.freeFromGlobal(t)
  }

  private def getValue(name : String,
                       enclosingFunction : String,
                       isIndirection : Boolean = false) : CCExpr =
    getValue(scope.lookupVar(name, enclosingFunction), isIndirection)
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
    setValue(scope.lookupVar(name, enclosingFunction), t, isIndirection)
  private def setValue(ind: Int, t : CCExpr,
                       isIndirection : Boolean) : Unit = {
    val actualInd = getValue(ind, false).typ match {
      case stackPtr: CCStackPointer => stackPtr.targetInd
      case _ => ind
    }
    values = values.updated(actualInd, t)
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

  def getValues : Seq[CCExpr] =
    values.toList
  def getValuesAsTerms : Seq[ITerm] =
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

  private def isHeapRead(t : CCExpr) =
    t.toTerm match {
      case IFunApp(f, _) if context.objectGetters contains f => true
      case _ => false
    }
  /*t.toTerm.isInstanceOf[IFunApp] &&
    t.toTerm.asInstanceOf[IFunApp] match {
      case Left(c) => c.sort.isInstanceOf[context.heap.HeapSort]
      case Right(f) => context.objectGetters contains f.fun
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
    val currentClauseNum = context.clausesSize
    val initSize = values.size

    context.inAtomicMode {
      pushVal(CCFormula(true, CCVoid, None))
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

  def atomicEvalFormula(exp : Exp, evalCtx : EvalContext) : CCFormula = {
    val initSize         = values.size

    context.inAtomicMode{
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
            val structType = context.structDefs(t.sort.name)
            val fieldAddress = structType.getFieldAddress(fieldSelectors)
            CCTerm(structType.setFieldTerm(t, rhs.toTerm, fieldAddress),
                   structType, rhs.srcInfo)
          case Right(f) =>
            val structType =
              context.structDefs(f.fun.asInstanceOf[MonoSortedIFunction].resSort.name)
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
    case _ : HeapModel.FunctionCall => ??? // TODO: handle other heap models
  }

  def handleArrayInitialization(arrayPtr  : CCHeapArrayPointer,
                                arraySize : CCExpr,
                                initStack : mutable.Stack[ITerm]): CCTerm = {
    val result =
      heapModel.allocAndInitArray(arrayPtr, arraySize.toTerm, initStack, values)

    val returnValue = processHeapResult(result)

    returnValue.getOrElse(throw new TranslationException(
      "Array initialization did not return a pointer."))
  }

  def handleUninitializedArrayDecl(arrayTyp         : CCHeapArrayPointer,
                                   sizeExpr         : Option[Constant_expression],
                                   isGlobalOrStatic : Boolean): CCTerm = {
    val sizeTerm = sizeExpr match {
      case Some(expr) =>
        Some(eval(expr.asInstanceOf[Especial].exp_)
             (EvalSettings(true), EvalContext()).toTerm)
      case None =>
        None
    }

    val result =
      heapModel.declUninitializedArray(arrayTyp, sizeTerm, isGlobalOrStatic, values)
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
        if (updatingPointedValue) {
          processHeapResult(
            heapModel.write(lhsVal.toTerm.asInstanceOf[IFunApp], rhsVal, values))
        } else if (lhsIsArraySelect) { // todo: this branch needs to be rewritten, it was hastily coded to deal with arrays inside structs.
          val newTerm = CCTerm(
            writeADT(lhsVal.toTerm.asInstanceOf[IFunApp],
                     rhsVal.toTerm, context.heap.userADTCtors, context.heap.userADTSels),
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
              } else CCTerm(context.heap.nullAddr(),
                            CCHeapPointer(context.heap, lhsVal.typ), rhsVal.srcInfo)
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
                      scope.updateVarType(lhsName, arrayPtr1,
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
        processHeapResult(
          heapModel.write(lhsVal.toTerm.asInstanceOf[IFunApp], newVal, values))
      } else {
        setValue(scope.lookupVar(asLValue(exp.exp_1), evalCtx.enclosingFunctionName),
                 getActualAssignedTerm(lhsVal, newVal),
                 isIndirection(exp.exp_1)) // todo get rid of indirections?
      }
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
      pushVal(popVal convertToType context.getType(exp.type_name_))
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
        processHeapResult(
          heapModel.write(lhsVal.toTerm.asInstanceOf[IFunApp], topVal, values))
      } else {
        setValue(scope.lookupVar(asLValue(preExp), evalCtx.enclosingFunctionName),
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
              if !(context.objectGetters contains fieldFun.fun) &&
                 (context.heap.userADTSels exists(_ contains fieldFun.fun)) => // an ADT
              val (fieldNames, rootTerm) = getFieldInfo(fieldFun)
              rootTerm match {
                case Left(c) =>
                  val rootInd: Int = scope.lookupVar(c.name, evalCtx.enclosingFunctionName)
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
//                    addGuard(context.heap.heapADTs.hasCtor(readObj, context.sortCtorIdMap(resSort)))
//                    pushVal(newTerm)
                  throw new UnsupportedCFragmentException(
                    getLineStringShort(srcInfo) +
                    " Stack pointers in combination with heap pointers")
              }
            case f : IFunApp if context.objectGetters contains f.fun => // a heap read (might also be from a heap array)
              val readFunApp = f.args.head.asInstanceOf[IFunApp] // sth like read(h, ...)
              val Seq(heapTerm, addrTerm) = readFunApp.args
              // todo: below type extraction is not safe!
              val heap = context.heap
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
                  CCTerm(addrTerm, CCHeapPointer(context.heap,
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
              else pushVal(processHeapResult(heapModel.read(v, values)).get)
            case  arr : CCHeapArrayPointer =>
              if(evalCtx.evaluatingLHS) pushVal(v)
              else pushVal(processHeapResult(heapModel.arrayRead(
                v, CCTerm(IIntLit(0), CCInt, srcInfo), values)).get)
            case _ => throw new TranslationException(
              "Cannot dereference non-pointer: " + v.typ + " " + v.toTerm)
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
      GetId.orString(exp) match {
        case "reach_error" =>
          /**
           * A special SV-COMP function used in the unreach-call category.
           * We directly rewrite this as `assert(0)`.
           */
          if(context.propertiesToCheck contains properties.Reachability)
            assertProperty(false, srcInfo, properties.Reachability)
          pushVal(CCFormula(true, CCInt, srcInfo))
        case name =>
          outputClause(srcInfo)
          handleFunction(name, initPred, 0)
      }

    case exp : Efunkpar =>
      val srcInfo = Some(getSourceInfo(exp))
      GetId.orString(exp) match {
        case "assert" | "static_assert" if exp.listexp_.size == 1 =>
          val property = exp.listexp_.head match {
            case a : Efunkpar
              if context.uninterpPredDecls contains(GetId.orString(a)) =>
              val args = a.listexp_.map(exp => atomicEval(exp, evalCtx))
              if(args.exists(a => a.typ.isInstanceOf[CCStackPointer])) {
                throw new TranslationException(
                  getLineStringShort(srcInfo) + " Unsupported operation: " +
                  "stack pointer argument to uninterpreted predicate.")
              }
              val pred = context.uninterpPredDecls(GetId.orString(a))
              context.atom(pred, args.map(_.toTerm))
            case interpPred : Efunkpar
              if context.interpPredDefs contains(GetId.orString(interpPred)) =>
              val args    = interpPred.listexp_.map(
                exp => atomicEval(exp, evalCtx)).map(_.toTerm)
              val formula = context.interpPredDefs(GetId.orString(interpPred))
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
              if context.uninterpPredDecls contains(GetId.orString(a)) =>
              val args = a.listexp_.map(exp => atomicEval(exp, evalCtx))
                          .map(_.toTerm)
              val pred = context.uninterpPredDecls(GetId.orString(a))
              context.atom(pred, args)
            case interpPred : Efunkpar
              if context.interpPredDefs contains (GetId.orString(interpPred)) =>
              val args = interpPred.listexp_.map(
                exp => atomicEval(exp, evalCtx)).map(_.toTerm)
              val formula = context.interpPredDefs(GetId.orString(interpPred))
              // the formula refers to pred arguments as IVariable(index)
              // we need to subsitute those for the actual arguments
              VariableSubstVisitor(formula.f, (args.toList, 0))
            case _ =>
              atomicEvalFormula(exp.listexp_.head, evalCtx).f
          }
          addGuard(property)
          pushVal(CCFormula(true, CCInt, srcInfo))
        case cmd@("chan_send" | "chan_receive") if (exp.listexp_.size == 1) =>
          val name = GetId.orString(exp.listexp_.head)
          (context.channels get name) match {
            case Some(chan) => {
              val sync = cmd match {
                case "chan_send"    => ParametricEncoder.Send(chan)
                case "chan_receive" => ParametricEncoder.Receive(chan)
              }
              outputClause(context.newPred(Nil, srcInfo), srcInfo, sync)
              pushVal(CCFormula(true, CCInt, srcInfo))
            }
            case None =>
              throw new TranslationException(
                name + " is not a declared channel")
          }
        case name@("malloc" | "calloc" | "alloca" | "__builtin_alloca")
          if !TriCeraParameters.parameters.value.useArraysForHeap => // todo: proper alloca and calloc
          val (typ, allocSize) = exp.listexp_(0) match {
            case exp : Ebytestype =>
              (context.getType(exp), CCTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))
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
              val allocatedAddr =
                processHeapResult(heapModel.alloc(objectTerm, values)).get

              pushVal(allocatedAddr)
            case CCTerm(sizeExp, typ, srcInfo) if typ.isInstanceOf[CCArithType] =>
              val addressRangeValue =
                processHeapResult(
                  heapModel.batchAlloc(objectTerm, sizeExp, arrayLoc, values)).get

              pushVal(addressRangeValue)
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
              (context.getType(exp), CCTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))
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
          throw new TranslationException("realloc is not supported.")
        case "free" =>
          val ptrExpr = atomicEval(exp.listexp_.head, evalCtx)
          processHeapResult(heapModel.free(ptrExpr, values))
          pushVal(CCTerm(0, CCVoid, srcInfo)) // free returns no value, push dummy
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
          for (e <- exp.listexp_)
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
          processHeapResult(heapModel.read(subexpr, values)).get
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
      val structInfo = context.structInfos.find(_.name == structType.shortName) match {
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
        processHeapResult(heapModel.write(evalExp.toTerm.asInstanceOf[IFunApp],
                                     topVal mapTerm (_ + op), values))
      } else {
        setValue(scope.lookupVar(asLValue(postExp), evalCtx.enclosingFunctionName),
                 getActualAssignedTerm(evalExp, topVal mapTerm (_ + op)),
                 isIndirection(postExp)) // todo get rid of indirection?
      }

    case exp : Evar =>
      // todo: Unify with EvarWithType, they should always be treated the same.
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
      pushVal(CCTerm(IIntLit(IdealInt(1)), CCInt, srcInfo))

    case exp : Earray =>
      val srcInfo = Some(getSourceInfo(exp))
      val arrayTerm : CCExpr = eval(exp.exp_1)
      val index : CCExpr = eval(exp.exp_2)

      import IExpression._
      arrayTerm.typ match {
        case array : CCHeapArrayPointer =>
          pushVal(processHeapResult(heapModel.arrayRead(arrayTerm,index, values)).get)
        case array : CCArray => // todo: move to separate method
          val readValue = CCTerm(
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

        val postGlobalVars : Seq[ITerm] = // todo : use ctx postglobal?
          for (v <- scope.GlobalVars.vars) yield {
            if (v.isStatic) {
              throw new TranslationException(
                "Static variables with contracts are not supported yet.")
              // todo: this should be easy to support, need to distinguish
              //       at a few locations the static variables belonging to
              //       that function only.
            }
            IExpression.i(v.sort newConstant(v.name + Literals.postExecSuffix)) //
            // todo: refactor
          }

        val globals : Seq[ITerm] =
          for (n <- 0 until scope.GlobalVars.size)
            yield getValue(n, false).toTerm

        val prePredArgs : Seq[ITerm] = globals ++ argTerms

        val resVar : Seq[CCVar] = scope.getResVar(context.getType(funDef))
        val postPredArgs : Seq[ITerm] =
          prePredArgs ++ postGlobalVars ++ resVar.map(c => IConstant(c.term))
        //postGlobalVars ++ argTerms ++ globals ++ resVar.map(c => IConstant(c.term))

        val preAtom  = ctx.prePred(prePredArgs)
        val postAtom = ctx.postPred(postPredArgs)

        assertProperty(preAtom, functionEntry.srcInfo,
                       properties.FunctionPrecondition(name,functionEntry.srcInfo))

        addGuard(postAtom)

        for (((c, t), n) <- (postGlobalVars.iterator zip
                             scope.GlobalVars.formalTypes.iterator).zipWithIndex)
          setValue(n, CCTerm(c, t, None), false) // todo: srcInfo?

        resVar match {
          case Seq(v) => pushVal(CCTerm(v.term, v.typ, v.srcInfo))
          case Seq()  => pushVal(CCTerm(0, CCVoid, None)) // push a dummy result
        }
      case None =>
        context.uninterpPredDecls get name match {
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
    (context.functionDefs get name) match {
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

  private def checkPointerIntComparison(t1 : CCExpr, t2 : CCExpr) :
  (CCExpr, CCExpr) = {
    (t1.typ, t2.typ) match {
      case (_ : CCHeapPointer, _ : CCArithType) =>
        if (t2.toTerm != IIntLit(IdealInt(0)))
          throw new TranslationException("Pointers can only compared with `null` or `0`. " +
                                         getLineString(t2.srcInfo))
        else
          (t1, CCTerm(context.heap.nullAddr(), t1.typ, t1.srcInfo)) // 0 to nullAddr()
      case (_: CCArithType, _: CCHeapPointer) =>
        if (t1.toTerm != IIntLit(IdealInt(0)))
          throw new TranslationException("Pointers can only compared with `null` or `0`. " +
                                         getLineString(t2.srcInfo))
        else
          (CCTerm(context.heap.nullAddr(), t2.typ, t2.srcInfo), t2) // 0 to nullAddr()
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
