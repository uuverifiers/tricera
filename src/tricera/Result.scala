package tricera

import ap.parser.{IFormula, IConstant}
import tricera.Util.SourceInfo
import ap.terfor.ConstantTerm
import ap.theories.{Heap}

/**
 * Special constant class to keep track of constants corresponding
 * to program variables (function parameters and global variables)
 * in the original program.
*/
case class ProgVarProxy(
  _name: String,
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
  override def toString: String = f"${super.toString()}`${state.toString()}`${scope.toString()}"

/*
  def isPreExecHeap(heapInfo: HeapInfo): Boolean = {
    isPreExec && heapInfo.isHeap(this)
  }

  def isPostExecHeap(heapInfo: HeapInfo): Boolean = {
    isPostExec && heapInfo.isHeap(this)
  }
*/
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
//  def apply(c: ConstantTerm): IFuncParam = new IFuncParam(c)
//  def unapply(p: IFuncParam): Option[ConstantTerm] = Some(p.c)
}

object ConstantAsProgVarProxy {
  def unapply(constant: IConstant): Option[ProgVarProxy] =
    constant match {
      case IConstant(p @ ProgVarProxy(_,_,_,_)) => Some(p)
      case _ => None
  }
}

case class ProgVarContextException(msg: String) extends Exception(msg)

/*
class FuncParamUtils(preSuffix: String, postSuffix: String) {
  def isPreCondName(p: IFuncParam): Boolean = {
    p.toString().endsWith(preSuffix)
  }

  def isPostCondName(p: IFuncParam): Boolean = {
    p.toString().endsWith(postSuffix)
  }

  def isPreCondHeap(p: IFuncParam, heapInfo: HeapInfo): Boolean = {
    isPreCondName(p) && heapInfo.isHeap(stripPreSuffix(p))
  }

  def isPostCondHeap(p: IFuncParam, heapInfo: HeapInfo): Boolean = {
    isPostCondName(p) && heapInfo.isHeap(stripPostSuffix(p))
  }

  def stripPreSuffix(p: IFuncParam): IFuncParam = {
    stripAnySuffix(p, preSuffix)
  }

  def stripPostSuffix(p: IFuncParam): IFuncParam = {
    stripAnySuffix(p, postSuffix)
  }

  def stripSuffix(p: IFuncParam): IFuncParam = {
    val stripped = stripPreSuffix(p)
    if (stripped != p) {
      stripped
    } else {
      stripPostSuffix(p)
    }
  }

  private def stripAnySuffix(p: IFuncParam, suffix: String): IFuncParam = {
    val name = p.toString()
    if (name.endsWith(suffix)) {
      IFuncParam(new ConstantTerm(name.dropRight(suffix.size)))
    } else {
      p
    }
  }
}
*/

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
  preCondition: PreCondition,
  postCondition: PostCondition,
  loopInvariants: List[LoopInvariant]) {
}

sealed trait Result {
  def isSolution: Boolean = false
  def isCounterExample: Boolean = false
  def isEmpty: Boolean = false
}

// SSSOWO: Add loop invariants
case class Solution(
  val functionInvariants: Seq[FunctionInvariants]) extends Result {

  override def isSolution: Boolean = true
  def hasFunctionInvariants = !functionInvariants.isEmpty
  def hasLoopInvariants = false

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
