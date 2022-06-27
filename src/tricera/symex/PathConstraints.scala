package tricera.symex
import lazabs.horn.bottomup.HornClauses._
import ap.parser.IExpression._
import ap.parser.IFormula

object PathConstraints {
  /**
   * @param clauses clauses to generate path constraints from
   * @return a map from each uninterpreted pred in clauses to its path constraint
   */
  def apply(clauses : Seq[Clause]) :
    Map[Predicate, IFormula] = {
    // we will generate the path condition for each predicate until
    // a fixed point is reached
    val predsToProcess = new scala.collection.mutable.HashSet[Predicate]
    // initially, all predicates must be processed
//    val normalizedClauses = clauses.map(normalize)

    val preds = clauses.flatMap(_.predicates).toSet
    preds.foreach(predsToProcess add)

    // predicate path constraints will be collected in this map
    val predPathConstraints =
      new scala.collection.mutable.HashMap[Predicate, IFormula]
    // initially, all predicate have the path constraint "true"
    preds.foreach(p => predPathConstraints += ((p, i(true))))

    // a map from a pred p to preds that have p in their bodies
    // i.e., if the path constraint of p is updated, this map points to
    // predicates that will get immediately effected
    val predsThisPredAffects: Map[Predicate, Seq[Predicate]] =
    (for (p <- preds) yield {
      (p, clauses.filter(clause =>
        clause.bodyPredicates.contains(p)).map(_.head.pred))
    }).toMap

    while (predsToProcess nonEmpty) {
      val p = predsToProcess.head
      predsToProcess -= p
      val incomingClauses =
        clauses.filter(clause => clause.head.pred == p)

      val incomingPathConstraints = for (clause <- incomingClauses) yield {
        clause.bodyPredicates.map(bodyPred =>
          predPathConstraints(bodyPred)).reduceOption(_ &&& _).
          getOrElse(i(true)) &&& clause.constraint
      }
      val pathConstraint =
        incomingPathConstraints.reduceOption(_ ||| _).getOrElse(i(true))

      val simpPathConstraint = pathConstraint
//      val simpPathConstraint =
//        ap.SimpleAPI.withProver { p =>
//        import p._
//        addConstantsRaw(SymbolCollector constantsSorted pathConstraint)
//        asIFormula(asConjunction(pathConstraint))
//      }

      if (simpPathConstraint != predPathConstraints(p)) {
        predPathConstraints += ((p, simpPathConstraint))
        predsThisPredAffects(p).foreach(predsToProcess add)
      } else {
        // nothing, the path constraint for p reached a fixpoint
      }
    }
    predPathConstraints.toMap
  }
}
