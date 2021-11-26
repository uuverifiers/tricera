package tricera.acsl

import ap.parser.IExpression

// IDEA: Create trait `Annotation` and extend when multiple such classes gets
//       added (e.g. `LoopAnnotation`, `GlobalPredicate` etc.) if overlap in
//       functionality. Unsure what functionality CCReader will require here
//       eventually.
//       e.g. def toHorn(???) : Clauses
class FunctionContract(val pre  : IExpression, 
                    /* TODO: Add assigns as e.g:
                     * val assigns : Seq[CCVar/IConstant],
                     * val assigns : HashMap[String, CCVar/IConstant],*/
                       val post : IExpression
                       ) {

  override def toString : String = {
    s"Precondition:\n$pre\nPostcondition:\n$post"
  }

}
