package tricera.acsl

import ap.parser.IFormula

class FunctionContract(val pre  : IFormula, val post : IFormula, val assignsAssert : IFormula, val assignsAssume : IFormula) {
  override def toString : String = {
    s"Pre:  $pre\nPost: $post\n" + 
    s"Assigns (in asserts): $assignsAssert\nAssigns (in assumes): $assignsAssume"
  }

}
