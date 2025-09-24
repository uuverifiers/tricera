/**
 * Copyright (c) 2025 Scania CV AB. All rights reserved.
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
package tricera

import ap.parser.{IFormula, IConstant}
import tricera.Util.SourceInfo
import ap.terfor.ConstantTerm
import ap.theories.{Heap}
import ap.parser.SymbolCollector
import ap.parser.ConstantSubstVisitor

/**
 * Special constant class to keep track of constants corresponding
 * to program variables (function parameters and global variables)
 * in the original program.
*/
case class ProgVarProxy(
  private val _name: String,
  state: ProgVarProxy.State,
  scope: ProgVarProxy.Scope,
  private val _isPointer: Boolean)
  extends ConstantTerm(_name) {

  import tricera.ProgVarProxy.State._
  import tricera.ProgVarProxy.Scope._

  def isPreExec: Boolean = state == PreExec
  def isPostExec: Boolean = state == PostExec
  def isResult: Boolean = state == Result
  def isParameter: Boolean = scope == Parameter
  def isGlobal: Boolean = scope == Global
  def isPointer: Boolean = _isPointer

  override def clone: ProgVarProxy = ProgVarProxy(name, state, scope, _isPointer)
  override def toString: String = f"${super.toString()}`${state.toString()}`${scope.toString()}${if (isPointer) {"`Pointer"} else {""}}"
}

object ProgVarProxy {
  sealed trait State
  object State {
    case object Current extends State
    case object PreExec extends State
    case object PostExec extends State
    case object Result extends State
  }
  import State._

  sealed trait Scope
  object Scope {
    case object Global extends Scope
    case object Local extends Scope
    case object Parameter extends Scope
    case object Temporary extends Scope
  }
  import Scope._
}

object ConstantAsProgVarProxy {
  def unapply(constant: IConstant): Option[ProgVarProxy] =
    constant match {
      case IConstant(p @ ProgVarProxy(_,_,_,_)) => Some(p)
      case _ => None
  }
}

case class ProgVarContextException(msg: String) extends Exception(msg)

case class Invariant(
  expression: IFormula,
  heapInfo: Option[HeapInfo],
  sourceInfo: Option[SourceInfo]) {}

sealed trait InvariantContext

case class LoopInvariant (
  expression: IFormula,
  heapInfo: Option[HeapInfo],
  sourceInfo: SourceInfo) extends InvariantContext {}

case class PreCondition(invariant: Invariant) extends InvariantContext {
  def isCurrentHeap(varProxy: ProgVarProxy): Boolean = invariant.heapInfo match {
    case Some(heapInfo) => varProxy.isPreExec && heapInfo.isHeap(varProxy)
    case _ => false
  }
}

case class PostCondition(invariant: Invariant) extends InvariantContext {
  def isCurrentHeap(varProxy: ProgVarProxy): Boolean = invariant.heapInfo match {
    case Some(heapInfo) => varProxy.isPostExec && heapInfo.isHeap(varProxy)
    case _ => false
  }
}

case class FunctionInvariants(
  id: String,
  isSrcAnnotated: Boolean,
  preCondition: PreCondition,
  postCondition: PostCondition,
  loopInvariants: List[LoopInvariant]) {

  /**
    * Calculates the "meet" of two FunctionInvariants instances'
    * pre- and post-conditions. It is defined by
    *   [pre1, post1] meet [pre2, post2] <=>
    *   [(pre1 \/ pre2), (pre1 => post1) /\ (pre2 => post2)]
    * 
    * Any loop invariants will be aggregated into a single set.
    *
    * @param other The pre-/post-condition pair to meet with.
    * @return 
    */
  def meet(other: FunctionInvariants): FunctionInvariants = {
    def buildCommonConstantMap(constantSets: scala.collection.Set[ConstantTerm]*): Map[ConstantTerm, IConstant] = {
      constantSets
        .flatten
        // Using toString is a bit ugly. But since we are dealing
        // with different types of ConstantTerms, this will make
        // instances with same name but different other properties,
        // be different keys in the map.
        .groupBy(c => c.toString)
        .flatMap({ case (key, constants) =>
          val term = new IConstant(constants.head)
          constants.map(c => (c, term))
        })
    }
    
    val PreCondition(Invariant(pre1org, preHeapInfo, preSourceInfo)) = preCondition
    val PostCondition(Invariant(post1org, postHeapInfo, postSrcInfo)) = postCondition
    val PreCondition(Invariant(pre2org, _, _)) = other.preCondition
    val PostCondition(Invariant(post2org, _, _)) = other.postCondition
 
    val const2Common = buildCommonConstantMap(
      SymbolCollector.constants(pre1org),
      SymbolCollector.constants(pre2org),
      SymbolCollector.constants(post1org),
      SymbolCollector.constants(post2org))
    
    val pre1 = ConstantSubstVisitor.apply(pre1org, const2Common)
    val pre2 = ConstantSubstVisitor.apply(pre2org, const2Common)
    val post1 = ConstantSubstVisitor.apply(post1org, const2Common)
    val post2 = ConstantSubstVisitor.apply(post2org, const2Common)

    // TODO: 2025-05-19 Decide if we should run expressions through the
    //   SimpleAPI.simplify(). Doing so seems to mess up later stages, mainly
    //   because they treat conjunctions and disjunctions differently. That is,
    //   some parts of the code gives special treatment to e.g. disjunctions,
    //   but no such special treatment would be done for the corresponding
    //   conjunction (obtained by De'Morgans law).
    FunctionInvariants(
      id,
      isSrcAnnotated,
      PreCondition(Invariant((pre1 ||| pre2), preHeapInfo, preSourceInfo)),
      PostCondition(Invariant((pre1 ===> post1) &&& (pre2 ===> post2), postHeapInfo, postSrcInfo)),
      loopInvariants ::: other.loopInvariants)
  }
}

sealed trait Result {
  def isSolution: Boolean = false
  def isCounterExample: Boolean = false
  def isEmpty: Boolean = false
}

case class Solution(
  val functionInvariants: Seq[FunctionInvariants],
  val disassociatedLoopInvariants: Seq[LoopInvariant])
  extends Result {

  override def isSolution: Boolean = true
  def hasFunctionInvariants = !functionInvariants.isEmpty
  def hasLoopInvariants =
    functionInvariants.exists(i => !i.loopInvariants.isEmpty) ||
    !disassociatedLoopInvariants.isEmpty

  def isHeapUsed: Boolean = { 
    functionInvariants.exists(
      i => 
        i.preCondition.invariant.heapInfo.isDefined || 
        i.postCondition.invariant.heapInfo.isDefined ||
        i.loopInvariants.exists(l => l.heapInfo.isDefined)) }

  def apply(functionId: String) = { functionInvariants.find(i => i.id == functionId) }
}

case class CounterExample(
    counterExample: hornconcurrency.VerificationLoop.Counterexample) extends Result {
  override def isCounterExample = true
}

case class Empty() extends Result {
  override def isEmpty = true
}
