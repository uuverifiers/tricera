package tricera.acsl

import ap.parser.IFormula

// IDEA: Create trait `Annotation` and extend when multiple such classes gets
//       added (e.g. `LoopAnnotation`, `GlobalPredicate` etc.) if overlap in
//       functionality. Unsure what functionality CCReader will require here
//       eventually.
//       e.g. def toHorn(???) : Clauses
class FunctionContract(val pre  : IFormula,
                    /* TODO: Add assigns as e.g:
                     * val assigns : Seq[CCVar/IConstant],
                     * val assigns : HashMap[String, CCVar/IConstant],*/
                       val post : IFormula
                       ) {

  override def toString : String = {
    s"Precondition:\n$pre\nPostcondition:\n$post"
  }

}
