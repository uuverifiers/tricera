package tricera.postprocessor

import tricera.{Result, Solution, CounterExample, Empty, FunctionInvariants}
import tricera.Util.{SourceInfo, printlnDebug}
import ap.parser.IConstant

trait ResultProcessor {
  def apply(result: Result): Result = result match {
    case solution: Solution => applyTo(solution)
    case cex: CounterExample => applyTo(cex)
    case empty: Empty => applyTo(empty)
  }

  def applyTo(solution: Solution): Solution = {
    solution
  }

  def applyTo(counterExample: CounterExample): CounterExample = {
    counterExample
  }

  def applyTo(empty: Empty): Empty = {
    empty
  }
}

object DebugPrinter {
  def oldAndNew(
    processor: ResultProcessor,
    oldInvs: FunctionInvariants,
    newInvs: FunctionInvariants)
    = {
    printlnDebug(f"----- Applying ${processor} to ${oldInvs.id}.")
    printlnDebug("----- Precondition:")
    printlnDebug(oldInvs.preCondition.expression.toString)
    printlnDebug("----- New Precondition:")
    printlnDebug(newInvs.preCondition.expression.toString)
    printlnDebug("----- Postcondition:")
    printlnDebug(oldInvs.postCondition.expression.toString)
    printlnDebug("----- New Postcondition:")
    printlnDebug(newInvs.postCondition.expression.toString)
  }
}