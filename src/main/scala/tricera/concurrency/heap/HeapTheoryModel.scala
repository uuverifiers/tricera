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

package tricera.concurrency.heap

import ap.basetypes.IdealInt
import ap.parser.IExpression._
import ap.parser._
import ap.types.MonoSortedIFunction
import lazabs.horn.bottomup.HornClauses.toPrologSyntax
import tricera.acsl.ACSLTranslator
import tricera.concurrency.CCReader.CCAssertionClause
import tricera.concurrency.ccreader.CCExceptions.TranslationException
import tricera.concurrency.ccreader._
import tricera.concurrency.SymexContext
import tricera.concurrency.concurrent_c.Absyn.{Function_def, Stm}
import tricera.params.TriCeraParameters
import tricera.properties
import tricera.properties.Property

import scala.collection.mutable

final class HeapTheoryFactory(context : SymexContext,
                              scope   : CCScope) extends HeapModelFactory {
  import HeapModel._

  private val heapVarName = "@h"
  private val memCleanupVarName = "@v_cleanup"

  override val requiredVars : Seq[VarSpec] =
    Seq(VarSpec("@h",
                CCHeap(context.heap),
                isGlobal = true,
                context.heap.emptyHeap())) ++
    /**
     * For checking [[properties.MemValidCleanup]], a prophecy variable is used.
     */
    (if ((context.propertiesToCheck contains properties.MemValidCleanup) ||
         context.propertiesToCheck.contains(properties.MemValidTrack) &&
         TriCeraParameters.get.useMemCleanupForMemTrack)
       Seq(VarSpec(memCleanupVarName,
                   CCHeapPointer(context.heap, CCVoid),
                   isGlobal = true,
                   context.heap.nullAddr()))
     else Nil)

  override def requiredPreds : Seq[PredSpec] = Nil

  override def apply(res : Resources) : HeapModel = {
    val heapVar       = res.vars(heapVarName)
    val memCleanupVar = res.vars.get(memCleanupVarName)
    new HeapTheoryModel(context, scope, heapVar, memCleanupVar)
  }

  override def getFunctionsToInject : Map[String, Function_def] = Map()
  override def getInitCodeToInject : Seq[String] = Seq()
}

class HeapTheoryModel(context           : SymexContext,
                      scope             : CCScope,
                      val heapVar       : CCVar, // TODO: make these private, currently not because of ACSL
                      val memCleanupVar : Option[CCVar]) extends HeapModel {
  import HeapModel._

  private def updateValue(v : CCVar, newVal : CCTerm, s : Seq[CCTerm]) : Seq[CCTerm] = {
    assert(v == heapVar || memCleanupVar.nonEmpty && v == memCleanupVar.get)
    s.updated(scope.GlobalVars.lastIndexWhere(v), newVal)
  }

  private def getValue(v : CCVar, s : Seq[CCTerm]) = {
    assert(v == heapVar || memCleanupVar.nonEmpty && v == memCleanupVar.get)
    s(scope.GlobalVars.lastIndexWhere(v))
  }

  override def read(p : CCTerm, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult = {
    val (objectGetter, typ : CCType) = p.typ match {
      case typ: CCHeapPointer =>
        (context.sortGetterMap(typ.typ.toSort), typ.typ)
      case _ => throw new TranslationException(
        "Can only read from heap pointers! (" + p + ")")
    }
    val readObj  = context.heap.read(getValue(heapVar, s).toTerm, p.toTerm)

    var assumptions = List[CCTerm]()
    var assertions = List[(CCTerm, Property)]()

    if (context.propertiesToCheck.contains(properties.MemValidDeref)) {
      val safetyFormula = CCTerm.fromFormula(
        context.heap.heapADTs.hasCtor(readObj, context.sortCtorIdMap(typ.toSort)),
        CCInt, p.srcInfo)
      assertions = (safetyFormula, properties.MemValidDeref) :: assertions
      assumptions = safetyFormula :: assumptions
      // todo: add tester methods for user ADT sorts?
    }
    SimpleResult(
      returnValue = Some(CCTerm.fromTerm(objectGetter(readObj), typ, p.srcInfo)),
      nextState   = s,
      assumptions = assumptions,
      assertions  = assertions
      )
  }

  override def alloc(o : CCTerm, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult = {
    val objTerm  = context.sortWrapperMap(o.typ.toSort)(o.toTerm)
    val newAlloc = context.heap.alloc(getValue(heapVar, s).toTerm, objTerm)
    val newHeapTerm = CCTerm.fromTerm(context.heap.newHeap(newAlloc),
                             CCHeap(context.heap),
                             o.srcInfo)
    val newAddrTerm = CCTerm.fromTerm(context.heap.newAddr(newAlloc),
                             CCHeapPointer(context.heap, o.typ),
                             o.srcInfo)
    var nextState = updateValue(heapVar, newHeapTerm, s)

    if ((context.propertiesToCheck contains properties.MemValidCleanup) ||
        (context.propertiesToCheck.contains(properties.MemValidTrack) &&
         TriCeraParameters.get.useMemCleanupForMemTrack)) {
      /**
       * Nondeterministically write the address to the prophecy[[memCleanupVar]]
       * I.e., nondet ==> [[memCleanupVar]]] = allocatedAddr
       */
      val nondetTerm =
        IConstant(scope.getFreshEvalVar(CCBool, None, name = "nondet").term)
      val prophTerm = getValue(memCleanupVar.get, nextState)
      val newProphTerm = CCTerm.fromTerm(
        IExpression.ite(
          nondetTerm === ap.theories.ADT.BoolADT.True,
          newAddrTerm.toTerm,
          prophTerm.toTerm), prophTerm.typ, None)
      nextState = updateValue(memCleanupVar.get, newProphTerm, nextState)
    }

    SimpleResult(returnValue = Some(newAddrTerm),
                 nextState   = nextState)
  }

  override def write(p    : CCTerm,
                     o    : CCTerm,
                     s    : Seq[CCTerm],
                     loc  : CCTerm) : HeapOperationResult = {
    val newHeapTerm = CCTerm.fromTerm(
      context.heap.write(getValue(heapVar, s).toTerm, p.toTerm, o.toTerm),
      CCHeap(context.heap),
      o.srcInfo)

    var assumptions = List[CCTerm]()
    var assertions = List[(CCTerm, Property)]()

    if (context.propertiesToCheck.contains(properties.MemValidDeref)) {
      // We need to read the current heap to check if it is OK to write.
      val curO = CCTerm.fromTerm(
        context.heap.read(getValue(heapVar, s).toTerm, p.toTerm),
        CCHeap(context.heap),
        o.srcInfo)

      val safetyFormula = CCTerm.fromFormula(
        context.heap.heapADTs.hasCtor(curO.toTerm, context.sortCtorIdMap(o.typ.toSort)),
        CCInt, p.srcInfo)
      assertions = (safetyFormula, properties.MemValidDeref) :: assertions
      assumptions = safetyFormula :: assumptions
    }

    SimpleResult(
      returnValue = None,
      nextState   = updateValue(heapVar, newHeapTerm, s),
      assumptions = assumptions,
      assertions  = assertions
      )
  }

  override def free(p: CCTerm, s: Seq[CCTerm], loc : CCTerm): HeapOperationResult = {
    var assertions  = List[(CCTerm, Property)]()
    var nextState   = s

    p.typ match {
      case heapPtr: CCHeapPointer =>
        // To 'free' `p`, we write the default object to its location.
        if (context.propertiesToCheck.contains(properties.MemValidFree)) {
          /**
           * Add an assertion that `ptrExpr` is safe to free.
           * Checking [[tricera.concurrency.ccreader.CCHeapPointer.heap.isAlloc]]
           * is not sufficient: freed locations are marked by writing the
           * default object to them, so we need to check that
           * read(h, p) =/= defObj. A free is also valid when p is nullAddr.
           */
          val readObj = context.heap.read(getValue(heapVar, s).toTerm, p.toTerm)
          val assertion = CCTerm.fromFormula(p.toTerm === context.heap.nullAddr() |||
                                    readObj =/= context.heap._defObj, CCInt, p.srcInfo)
          assertions = (assertion, properties.MemValidFree) :: assertions
        }

        val writeResult =
          write(p, CCTerm.fromTerm(heapPtr.heap._defObj, heapPtr.typ, p.srcInfo), nextState, loc)

        nextState = writeResult.asInstanceOf[SimpleResult].nextState

        if ((context.propertiesToCheck contains properties.MemValidCleanup) ||
            (context.propertiesToCheck.contains(properties.MemValidTrack) &&
             TriCeraParameters.get.useMemCleanupForMemTrack)) {
          /**
           * Set [[memCleanupVar]] back to NULL, if the freed address
           * is the same as the one stored.
           */
          val memCleanupTerm    = getValue(memCleanupVar.get, nextState)
          val newMemCleanupTerm = CCTerm.fromTerm(
            IExpression.ite(memCleanupTerm.toTerm === p.toTerm,
                            context.heap.nullAddr(), memCleanupTerm.toTerm),
            memCleanupTerm.typ, None)
          nextState = updateValue(memCleanupVar.get, newMemCleanupTerm, nextState)
        }
      case arrayPtr: CCHeapArrayPointer =>
        // todo: what about ADTs?
        if (context.propertiesToCheck.contains(properties.MemValidFree)) {
          arrayPtr.arrayLocation match {
            case ArrayLocation.Heap =>
              /**
               * Assert that either `t` is `null`, or
               * forall ind. t[ind] =/= defObj
               * (or equivalently forall ind. read(h, nth(t, ind)) =/= defObj)
               */
              val ind = scope.getFreshEvalVar(CCInt, p.srcInfo)
              val readAddr = context.heap.nth(p.toTerm, ind.term)
              val readObj = context.heap.read(getValue(heapVar, nextState).toTerm, readAddr)
              val assertion = CCTerm.fromFormula(p.toTerm === context.heap.nullAddr() |||
                                        (context.heap.within(p.toTerm, readAddr) ==>
                                         (readObj =/= context.heap._defObj)), CCInt, p.srcInfo)
              assertions = (assertion, properties.MemValidFree) :: assertions
            case _ =>
              /**
               * Freeing non-heap memory is undefined behaviour.
               */
              assertions = (CCTerm.fromFormula(i(false), CCInt, p.srcInfo), properties.MemValidFree) :: assertions
          }
        }

        // This is a side effect: the heap variable is updated with the result of batchWrite.
        val newHeapTerm = CCTerm.fromTerm(
          context.heap.batchWrite(getValue(heapVar, nextState).toTerm, p.toTerm, context.defObj()),
          heapVar.typ, p.srcInfo)
        nextState = updateValue(heapVar, newHeapTerm, nextState)

        if ((context.propertiesToCheck contains properties.MemValidCleanup) ||
            (context.propertiesToCheck.contains(properties.MemValidTrack) &&
             TriCeraParameters.get.useMemCleanupForMemTrack)) {
          /**
           * Set [[memCleanupVar]] back to NULL, if the beginning of
           * the freed address block is the same as the one stored.
           */
          val memCleanupTerm    = getValue(memCleanupVar.get, nextState)
          val newMemCleanupTerm = CCTerm.fromTerm(
            IExpression.ite(memCleanupTerm.toTerm === context.heap.nth(p.toTerm, 0),
                            context.heap.nullAddr(), memCleanupTerm.toTerm),
            memCleanupTerm.typ, None)
          nextState = updateValue(memCleanupVar.get, newMemCleanupTerm, nextState)
        }

      case _ =>
        /**
         * Freeing a non-heap pointer.
         */
        if (context.propertiesToCheck.contains(properties.MemValidFree)) {
          assertions = (CCTerm.fromFormula(i(false), CCInt, p.srcInfo), properties.MemValidFree) :: assertions
        }
    }

    SimpleResult(
      returnValue = None,
      nextState   = nextState,
      assertions  = assertions
      )
  }

  override def batchAlloc(o        : CCTerm,
                          size     : ITerm,
                          arrayLoc : ArrayLocation.Value,
                          s        : Seq[CCTerm]) : HeapOperationResult = {
    val newBatchAlloc =
      context.heap.batchAlloc(getValue(heapVar, s).toTerm,
                              context.sortWrapperMap(o.typ.toSort)(o.toTerm), size)
    val newHeapTerm = CCTerm.fromTerm(context.heap.newBatchHeap(newBatchAlloc),
                             CCHeap(context.heap),
                             o.srcInfo)
    val newAddrRange = CCTerm.fromTerm(context.heap.newAddrRange(newBatchAlloc),
                                       CCHeapArrayPointer(context.heap, o.typ, arrayLoc),
                                       o.srcInfo)
    var nextState = updateValue(heapVar, newHeapTerm, s)

    if (arrayLoc == ArrayLocation.Heap &&
        ((context.propertiesToCheck contains properties.MemValidCleanup) ||
         (context.propertiesToCheck.contains(properties.MemValidTrack) &&
          TriCeraParameters.get.useMemCleanupForMemTrack))) {
      val nondetTerm  =
        IConstant(scope.getFreshEvalVar(CCBool, None, name = "nondet").term)
      val prophTerm = getValue(memCleanupVar.get, nextState)
      val newProphTerm = CCTerm.fromTerm(
        IExpression.ite(
          nondetTerm === ap.theories.ADT.BoolADT.True & size > 0,
          context.heap.nth(newAddrRange.toTerm, 0),
          prophTerm.toTerm), prophTerm.typ, None)
      nextState = updateValue(memCleanupVar.get, newProphTerm, nextState)
    }

    SimpleResult(
      returnValue = Some(newAddrRange),
      nextState = nextState
      )
  }

  override def arrayRead(arr   : CCTerm,
                         index : CCTerm,
                         s     : Seq[CCTerm],
                         loc   : CCTerm) : HeapOperationResult = {
    val arrType = arr.typ.asInstanceOf[CCHeapArrayPointer]
    val readAddress = CCTerm.fromTerm(context.heap.nth(arr.toTerm, index.toTerm),
                             CCHeapPointer(context.heap, arrType.elementType),
                             arr.srcInfo)

    val readResult = read(readAddress, s, loc)

    val boundsAssertion =
      if (context.propertiesToCheck.contains(properties.MemValidDeref)) {
        val assertion = CCTerm.fromFormula(
          context.heap.within(arr.toTerm, readAddress.toTerm), CCInt, arr.srcInfo)
        Seq((assertion, properties.MemValidDeref))
      } else {
        Seq.empty
      }

    readResult match {
      case SimpleResult(retVal, nextState, assumptions, assertions) =>
        SimpleResult(retVal, nextState, assumptions, assertions ++ boundsAssertion)
      case _ =>
        throw new TranslationException("Array read returned something other" +
                                       s"than a SimpleResult: $arr[$index]")
    }
  }

  override def arrayWrite(arr   : CCTerm,
                          index : CCTerm,
                          value : CCTerm,
                          s     : Seq[CCTerm],
                          loc   : CCTerm) : HeapOperationResult = {
    val arrType = arr.typ.asInstanceOf[CCHeapArrayPointer]
    val writeAddress = CCTerm.fromTerm(context.heap.nth(arr.toTerm, index.toTerm),
                              CCHeapPointer(context.heap, arrType.elementType),
                              arr.srcInfo)

    val writeResult = write(writeAddress, value, s, loc)

    val boundsAssertion =
      if (context.propertiesToCheck.contains(properties.MemValidDeref)) {
        val assertion = CCTerm.fromFormula(
          context.heap.within(arr.toTerm, writeAddress.toTerm), CCInt, index.srcInfo)
        Seq((assertion, properties.MemValidDeref))
      } else {
        Seq.empty
      }

    writeResult match {
      case SimpleResult(retVal, nextState, assumptions, assertions) =>
        SimpleResult(retVal, nextState, assumptions, assertions ++ boundsAssertion)
      case _ =>
        throw new TranslationException("Array write returned something other" +
                                       s"than a SimpleResult: $arr[$index]")
    }
  }

  override def allocAndInitArray(arrayPtr     : CCHeapArrayPointer,
                                 size         : ITerm,
                                 initializers : mutable.Stack[ITerm],
                                 s            : Seq[CCTerm],
                                 loc : CCTerm)
  : HeapOperationResult = {
    val objToAlloc = CCTerm.fromTerm(arrayPtr.elementType.getZeroInit, arrayPtr.elementType, None)
    val allocResult =
      batchAlloc(objToAlloc, size, ArrayLocation.Global, s).asInstanceOf[SimpleResult]

    var currentState = allocResult.nextState
    val arrayBasePtr = allocResult.returnValue.get.toTerm

    val arraySize = size match {
      case IIntLit(IdealInt(n)) => n.intValue
      case _ => throw new TranslationException(
        "Array initialization with a non-constant size is not supported.")
    }

    for (i <- 0 until arraySize) {
      val valueToInit = if (initializers.nonEmpty) {
        arrayPtr.elementType match {
          case structType: CCStruct => structType.getInitialized(initializers)
          case _ => initializers.pop()
        }
      } else {
        arrayPtr.elementType.getZeroInit
      }
      val wrappedValue = context.sortWrapperMap(Sort.sortOf(valueToInit))(valueToInit)

      val addrToWrite = context.heap.nth(arrayBasePtr, i)
      val writeResult = write(
        CCTerm.fromTerm(addrToWrite, CCHeapPointer(context.heap, arrayPtr.elementType), None),
        CCTerm.fromTerm(wrappedValue, arrayPtr.elementType, None),
        currentState, loc
        ).asInstanceOf[SimpleResult]

      currentState = writeResult.nextState
    }

    SimpleResult(returnValue = allocResult.returnValue, nextState = currentState)
  }

  override def declUninitializedArray(arrayTyp         : CCHeapArrayPointer,
                                      size             : Option[ITerm],
                                      isGlobalOrStatic : Boolean,
                                      s                : Seq[CCTerm])
  : HeapOperationResult = {
    val objValue = if (isGlobalOrStatic)
                     arrayTyp.elementType.getZeroInit
                   else arrayTyp.elementType.getNonDet
    val objTerm = CCTerm.fromTerm(objValue, arrayTyp.elementType, None)
    val loc = if (isGlobalOrStatic) ArrayLocation.Global
              else ArrayLocation.Stack
    size match {
      case Some(sizeTerm) =>
        batchAlloc(objTerm, sizeTerm, loc, s)
      case None =>
        SimpleResult(
          returnValue = Some(CCTerm.fromTerm(
            context.heap.addressRangeCtor(context.heap.nullAddr(), IIntLit(0)),
            CCHeapArrayPointer(context.heap, objTerm.typ, loc),
            objTerm.srcInfo)),
          nextState = s)
    }
  }

  override def getACSLPostStateHeapTerm(
    acslContext : ACSLTranslator.FunctionContext) : ITerm = {
    acslContext.getPostGlobalVar(heapVar.name).getOrElse(
      throw new TranslationException(
        s"ACSL context is missing the post-state heap variable '${heapVar.name}'")
      ).term
  }

  override def getACSLPreStateHeapTerm(
    acslContext : ACSLTranslator.FunctionContext) : ITerm = {
    acslContext.getOldVar(heapVar.name).getOrElse(
      throw new TranslationException(
        s"ACSL context is missing the pre-state (old) heap variable '${heapVar.name}'")
      ).term
  }

  override def getExitAssertions (exitPreds : Seq[CCPredicate])
  : Seq[CCAssertionClause] = {
    if ((context.propertiesToCheck contains properties.MemValidCleanup) ||
        (context.propertiesToCheck.contains(properties.MemValidTrack) &&
         TriCeraParameters.get.useMemCleanupForMemTrack)) {
      val heapInd       = scope.GlobalVars.lastIndexWhere(heapVar)
      val cleanupVarInd = scope.GlobalVars.lastIndexWhere(memCleanupVar.get)

      if (heapInd == -1 || cleanupVarInd == -1) {
        assert(false, "Could not find the heap term or the mem-cleanup" +
                      "prophecy variable term!")
        return Seq()
      }
      val newAssertions = for (finalPred <- exitPreds) yield finalPred match {
        case CCPredicate(_, args, _)
          if args.size > heapInd && args.size > cleanupVarInd &&
             args(heapInd).sort == context.heap.HeapSort &&
             args(cleanupVarInd).sort == context.heap.AddressSort =>

          val resVar = scope.getResVar(args.last.typ)
          context.mkRichAssertionClause(
            (args(cleanupVarInd).term === context.heap.nullAddr()) :-
            context.atom(finalPred,
                         scope.allFormalVarTerms.toList ++
                         resVar.map(v => IConstant(v.term)) take finalPred.arity),
            None, properties.MemValidCleanup)
        case _ =>
          assert(false, s"$finalPred does not contain the heap variable or " +
                         "the memory cleanup prophecy variable!")
          null
      }
      newAssertions.filter(_ != null)
    } else {
      Seq()
    }
  }
}
