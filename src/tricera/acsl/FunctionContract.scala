package tricera.acsl

import ap.parser.IFormula

class FunctionContract(val pre  : IFormula, val post : IFormula, val assigns : IFormula) {
  override def toString : String = {
    s"Pre:  $pre\nPost: $post\nAssigns: $assigns"
  }

}
