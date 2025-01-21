package tricera

import ap.parser.{IFormula, IConstant}
import tricera.Util.SourceInfo
import ap.terfor.ConstantTerm
import ap.theories.{Heap}

/**
 * Special constant class to keep track of constants corresponding
 * to function parameters in the original program.
*/
class IFuncParam(c: ConstantTerm) extends IConstant(c) {
  override def equals(other: Any): Boolean = other match {
    case that: IFuncParam => this.c == that.c
    case _ => false
  }
  //override def hashCode: Int = c.hashCode
}

object IFuncParam {
  def apply(c: ConstantTerm): IFuncParam = new IFuncParam(c)
  def unapply(p: IFuncParam): Option[ConstantTerm] = Some(p.c)
}

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

case class Invariant(
  expression: IFormula,
  utils: FuncParamUtils,
  sourceInfo: Option[SourceInfo]) {}

case class LoopInvariant(
  expression: IFormula,
  util: FuncParamUtils,
  sourceInfo: SourceInfo) {}

case class FunctionInvariants(
  id: String,
  preCondition: Invariant,
  postCondition: Invariant,
  loopInvariants: List[LoopInvariant]) {
}

sealed trait Result {
  def isSolution: Boolean = false
  def isCounterExample: Boolean = false
  def isEmpty: Boolean = false
}

// SSSOWO: Add loop invariants
case class Solution(
  val functionInvariants: Seq[FunctionInvariants],
  val heapInfo: Option[HeapInfo] = None) extends Result {

  override def isSolution: Boolean = true
  def hasFunctionInvariants = !functionInvariants.isEmpty
  def hasLoopInvariants = false

  def isHeapUsed: Boolean = heapInfo.isDefined
  def apply(functionId: String) = { functionInvariants.find(i => i.id == functionId) }
}

case class CounterExample(
    counterExample: hornconcurrency.VerificationLoop.Counterexample) extends Result {
  override def isCounterExample = true
}

case class Empty() extends Result {
  override def isEmpty = true
}
