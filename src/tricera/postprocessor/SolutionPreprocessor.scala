package tricera.postprocessor

import ap.types._
import ap.parser._
import IExpression.Predicate
import ap.theories.{ADT, TheoryRegistry}
import ADT.ADTProxySort

object SolutionProcessor {
  type Solution = Map[Predicate, IExpression]
}

trait SolutionProcessor {
  import SolutionProcessor._

  /**
   * A function to only process process the solutions for the passed list
   * of predicates. This doesn't need to be changed in new solution processors.
   * @param solution       : Solution to process
   * @param predsToProcess : Optionally, a list of predicates whose solutions
   *                         will be processed (default: all)
   * @return               : Returns the processed solution
   */
  def apply(solution       : Solution)
           (predsToProcess : Seq[Predicate] = solution.keys.toSeq): Solution = {
    for ((pred, expr) <- solution) yield
      (pred, (if (predsToProcess contains pred) apply(expr) else expr))
  }

  /**
   * This is the function that should be implemented in new solution processors
   * @param expr : IExpression to process
   * @return     : processed IExpression
   */
  def apply(expr : IExpression) : IExpression
}
