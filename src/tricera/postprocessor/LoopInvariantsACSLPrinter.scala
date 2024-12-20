package tricera.postprocessor

import tricera.{Result, Solution, LoopInvariant}

object LoopInvariantsACSLPrinter extends ResultProcessor {
  override def apply(result: Result) = {
    LoopInvariantsACSLPrinter()(result)
  }
}

final case class LoopInvariantsACSLPrinter() extends ResultProcessor {
  override def applyTo(solution: Solution) = solution match {
    case Solution(isHeapUsed, functionInvariants) => 
      printLoopInvariants(functionInvariants.flatMap(f => f.loopInvariants))
      solution
  }

  private def printLoopInvariants(invariants: Iterable[LoopInvariant]) = {
    println("/* loop invariants */")
    for (inv <- invariants) {
      println(f"\n/* loop invariant for the loop at line ${inv.sourceInfo.line} */")
      println( "/*@")
      println(f"  loop invariant ${ACSLLineariser.asString(inv.expression)};")
      println( "*/")
    }    
  }
}
