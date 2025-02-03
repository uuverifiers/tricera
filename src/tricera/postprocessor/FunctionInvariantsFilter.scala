package tricera.postprocessor

import tricera.{Result, Solution, FunctionInvariants}

/**
  * ResultProcessor to filter out FunctionInvariants that fulfills p.
  *
  * @param p predicate used to test function invariants
  */
case class FunctionInvariantsFilter(p: FunctionInvariants => Boolean)  extends ResultProcessor {
  override def applyTo(solution: Solution) = solution match {
    case Solution(functionInvariants) =>
      Solution(functionInvariants.filter(p))
  }
}