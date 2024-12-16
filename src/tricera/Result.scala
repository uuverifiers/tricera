package tricera

import ap.parser.IFormula
import tricera.Util.SourceInfo

case class LoopInvariant(expression: IFormula, sourceInfo: SourceInfo) {}

case class FunctionInvariants(
  preCondition: IFormula,
  postCondition: IFormula,
  loopInvariants: List[LoopInvariant]) {
}

sealed trait Result {
  def isSolution: Boolean = false
  def isCounterExample: Boolean = false
  def isEmpty: Boolean = false
}

case class Solution(val functionInvariants: Map[String, FunctionInvariants]) extends Result {
  override def isSolution: Boolean = true

  def apply(functionId: String) = { functionInvariants(functionId) }
}

case class CounterExample(
    counterExample: hornconcurrency.VerificationLoop.Counterexample) extends Result {
  override def isCounterExample = true
}

case class Empty() extends Result {
  override def isEmpty = true
}
