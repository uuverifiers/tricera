package tricera

import ap.parser.IFormula
import tricera.Util.SourceInfo

case class LoopInvariant(expression: IFormula, sourceInfo: SourceInfo) {}

case class FunctionInvariants(
  id: String,
  preCondition: IFormula,
  postCondition: IFormula,
  loopInvariants: List[LoopInvariant]) {
}

sealed trait Result {
  def isSolution: Boolean = false
  def isCounterExample: Boolean = false
  def isEmpty: Boolean = false
}

// SSSOWO: Add loop invariants
case class Solution(isHeapUsed: Boolean, val functionInvariants: Seq[FunctionInvariants]) extends Result {
  override def isSolution: Boolean = true
  def hasFunctionInvariants = !functionInvariants.isEmpty
  def hasLoopInvariants = false

  def apply(functionId: String) = { functionInvariants.find(i => i.id == functionId) }
}

case class CounterExample(
    counterExample: hornconcurrency.VerificationLoop.Counterexample) extends Result {
  override def isCounterExample = true
}

case class Empty() extends Result {
  override def isEmpty = true
}
