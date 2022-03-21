package tricera.acsl

import ap.parser.IFormula

class FunctionContract(
  val pre  : IFormula,
  val post : IFormula,
  val assignsAssert : IFormula,
  val assignsAssume : IFormula) {
  override def toString : String = {
    s"Pre:  $pre\n" +
    s"Post: $post\n" +
    s"Assigns (in asserts): $assignsAssert\n" +
    s"Assigns (in assumes): $assignsAssume"
  }

}
