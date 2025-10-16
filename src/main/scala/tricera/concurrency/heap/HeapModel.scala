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

import ap.parser._
import tricera.acsl.ACSLTranslator
import tricera.concurrency.CCReader._
import tricera.concurrency.ccreader._
import tricera.concurrency.SymexContext
import tricera.properties.Property

import scala.collection.mutable

object HeapModel {
  object ModelType extends Enumeration {
    val TheoryOfHeaps, Invariants = Value
  }

  /** Used to specify variables the model requires */
  case class VarSpec(name : String, typ : CCType, isGlobal : Boolean,
                     initialValue : ITerm)

  /** Used to specify (uninterpreted) predicates the model requires */
  case class PredSpec(name: String, argTypes: Seq[CCType])

  /** A container for all resources declared for the model. */
  case class Resources(
    vars  : Map[String, CCVar],
    preds : Map[String, CCPredicate]
  )

  sealed trait HeapOperationResult
  /**
   * Represents a simple heap operation that returns a value and updates state.
   *
   * @param returnValue The main result of the operation (e.g., data from a read
   *                    pointer from an alloc, or None from a write)
   * @param nextState   The complete, updated symbolic state of all variables.
   * @param assumptions Formulas to be conjoined with the current guard
   * @param assertions  Formulas that must be proven at this point
   */
  case class SimpleResult(
    returnValue : Option[CCTerm],
    nextState   : Seq[CCTerm],
    assumptions : Seq[CCTerm] = Seq.empty,
    assertions  : Seq[(CCTerm, Property)] = Seq.empty
  ) extends HeapOperationResult

  /**
   * Represents a heap operation that is implemented by calling a C function
   * using args. The result of the operation is the return value of the function.
   *
   * @param functionName The name of the C function to call.
   * @param args         The arguments to pass to the function.
   * @param resultType   The expected return type of the function.
   */
  case class FunctionCall(
    functionName : String,
    args         : Seq[CCTerm],
    resultType   : CCType // can be CCVoid
  ) extends HeapOperationResult


  def factory(mt      : ModelType.Value,
              context : SymexContext,
              scope   : CCScope) : HeapModelFactory =
    mt match {
      case ModelType.TheoryOfHeaps => new HeapTheoryFactory(context, scope)
      case ModelType.Invariants    => ??? // new InvariantsHeapFactory(context, scope)
    }

}


trait HeapModelFactory {
  import HeapModel._

  /** What CCVar declarations this model needs from the caller */
  def requiredVars : Seq[VarSpec]

  /** What CCPredicate declarations this model needs from the caller */
  def requiredPreds : Seq[PredSpec]

  /** Build the concrete model using the resources the caller allocated */
  def apply(resources: Resources): HeapModel
}

/**
 * An interface for heap memory models. Each operation also takes the current
 * state `s` (i.e., `values`) as input. The input `loc` is a term representing
 * the operation's location (i.e., meta-information).
 */
trait HeapModel {
  import HeapModel._

  def read (p : CCTerm, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult
  def write(p : CCTerm, o : CCTerm, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult
  def alloc(o : CCTerm, oType : CCType, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult
  def free (p : CCTerm, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult

  /**
   * Allocates an array of objects on the heap
   * @param o    The object to populate the array with
   * @param size The symbolic size of the array
   * @param arrayLoc  The location of the allocation
   * @param s    The current symbolic state of all variables
   */
  def batchAlloc(o        : CCTerm,
                 size     : ITerm,
                 arrayLoc : ArrayLocation.Value,
                 s        : Seq[CCTerm]) : HeapOperationResult

  /**
   * Reads an element from a heap array.
   * @param arr   The pointer to the start of the array
   * @param index The index to read from
   * @param s     The current symbolic state of all variables
   */
  def arrayRead(arr : CCTerm, index : CCTerm, s : Seq[CCTerm],
                loc : CCTerm) : HeapOperationResult

  def arrayWrite(arr : CCTerm, index : CCTerm, value : CCTerm,
                 s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult

   /**
   * A hook to handle allocation of an array with an
   * initializer list (e.g., `int a[] = {1, 2};`).
   * @param arrayPtr     The type of the array
   * @param size         The symbolic size of the array
   * @param initializers The stack of initializer values
   * @param s            The current symbolic state
   * @return The result of the operation, containing the pointer to the new
   *         initialized array and the updated program state.
   */
  def allocAndInitArray(
    arrayPtr     : CCHeapArrayPointer,
    size         : ITerm,
    initializers : mutable.Stack[ITerm],
    s            : Seq[CCTerm],
    loc          : CCTerm) : HeapOperationResult

   /**
   * Arrays declared without an explicit initializer list (e.g., `int a[n]`).
   * The size can be symbolic, and all elements get a default value.
   */
  def declUninitializedArray(arrayTyp         : CCHeapArrayPointer,
                             size             : Option[ITerm],
                             isGlobalOrStatic : Boolean,
                             forceNondetInit  : Boolean,
                             s                : Seq[CCTerm]) : HeapOperationResult

  /**
   * Generates any assertions that will be added to the exits of `entryFunction`.
   * For instance any assertions to check for memory leaks at exit from main.
   * @return A sequence of formulas to be asserted at exits from `entryFunction`
   */
  def getExitAssertions(exitPreds : Seq[CCPredicate]) : Seq[CCAssertionClause]

  /**
   * Hooks for the ACSL translator to get the pre/post-state heap terms.
   * These assume [[HeapTheoryModel]], so ideally should not be part of this
   * interface.
   * @param acslContext Provides access to contract-specific variables.
   * @return The ITerm for the heap in the pre-state.
   */
  def getACSLPreStateHeapTerm (acslContext : ACSLTranslator.FunctionContext) : ITerm
  def getACSLPostStateHeapTerm(acslContext : ACSLTranslator.FunctionContext) : ITerm
}
