package tricera.symex
import lazabs.horn.bottomup.HornClauses._
import ap.parser.IExpression._
import ap.parser.{DNFConverter, IBinJunctor, IFormula, LineariseVisitor, SymbolCollector}

object PathConstraints {
  /**
   * @param clauses clauses to generate path constraints from
   * @return a map from each uninterpreted pred in clauses to its path constraints
   */
  def apply(clauses : Seq[Clause]) : Map[Predicate, Set[IFormula]] = {
    // we will generate the path condition for each predicate until
    // a fixed point is reached
    val predsToProcess = new scala.collection.mutable.HashSet[Predicate]
    // initially, all predicates must be processed
    //    val normalizedClauses = clauses.map(normalize)

    val preds = clauses.flatMap(_.predicates).toSet
    preds.foreach(predsToProcess add)

    val theoriesInClauses= clauses.flatMap(_.theories)

    // predicate path constraints will be collected in this map
    val predPathConstraints =
      new scala.collection.mutable.HashMap[Predicate, Set[IFormula]]

    // initially, all predicate have the path constraint "true"
    preds.foreach(p => predPathConstraints += ((p, Set(i(true)))))

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

      implicit val fOrdering : Ordering[IFormula] =
        Ordering.by(f => f.hashCode())

      def genCombinations(l: List[List[Seq[IFormula]]]):
      List[List[Seq[IFormula]]] = l match {
        case hd :: _ =>
          hd.flatMap(i => genCombinations(l.tail).map(i :: _))
        case Nil =>
          List(Nil)
      }

      def distinctByHash (in : Iterable[IFormula]) : Iterable[IFormula] = {
        in.groupBy(_.hashCode()).map(_._2.head)
      }

      val pathConstraints : Set[IFormula] = (for (clause <- incomingClauses) yield {
        val conjunctsFromBodyPreds : List[List[Seq[IFormula]]] =
          clause.bodyPredicates.map(p => predPathConstraints(p).map(c =>
            LineariseVisitor(c, IBinJunctor.And)).toList).toList
        val conjunctsFromConstraint : Seq[IFormula] =
          LineariseVisitor(clause.constraint, IBinJunctor.And)
        // pathConjuncts is a list of path constraints for each body predicate
        // each path constraint is also a seq of conjuncts
        val pathConjuncts : List[List[Seq[IFormula]]] =
        genCombinations(conjunctsFromBodyPreds ++ List(List(conjunctsFromConstraint)))

        val pathConjoinedConjuncts : List[List[IFormula]] =
          pathConjuncts.map(cs => cs.map(conjs => distinctByHash(conjs).
          reduceOption(_ &&& _).getOrElse(i(true))))

        val conjoinedConstraints = pathConjoinedConjuncts.map(path =>
            path.map(c => distinctByHash(LineariseVisitor(c, IBinJunctor.And)).
              reduceOption(_ &&& _).getOrElse(i(true))).
              reduceOption(_ &&& _).getOrElse(i(true)))
        conjoinedConstraints
      }).flatten.sorted.toSet

      if (pathConstraints != predPathConstraints(p)) {
        predPathConstraints += ((p, pathConstraints))
        predsThisPredAffects(p).foreach(predsToProcess add)
      } else {
        // nothing, the path constraint for p reached a fixpoint
      }
    }
    (ap.SimpleAPI.withProver { prover =>
      import prover._
      addTheories(theoriesInClauses)
      for ((pred, constraints) <- predPathConstraints) yield {
        //         simplify each path constraint
        (pred, (for (constraint <- constraints) yield {
          addConstantsRaw(SymbolCollector constantsSorted constraint)
          asIFormula(asConjunction(constraint))
        }))
      }
    }).toMap
  }
}
