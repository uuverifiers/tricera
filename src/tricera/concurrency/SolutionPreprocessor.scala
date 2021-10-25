package tricera.concurrency
import ap.parser.IExpression
import ap.types._
import ap.parser._
import ap.theories.ADT.ADTProxySort
import ap.theories.{ADT, TheoryRegistry}

import scala.collection.mutable.{HashMap => MHashMap}

class SolutionPreprocessor { // make object? / parameters?
  //private val defaultRewritings = List(explodeStructs _)
  def apply(expr : IExpression) : IExpression = {
    import Rewriter._
    rewrite(expr, explodeADTs)
  }

  // a mapping from adt ctor expressions to a sequence of their field terms at postvisit
  val ADTFieldTerms = new MHashMap[ITerm, Seq[ITerm]]

  case class ADTTerm(t : ITerm, adtSort : ADTProxySort)
  object adtTermExploder extends CollectingVisitor[Object, IExpression] {
    def getADTTerm(t : IExpression) : Option[ADTTerm] = {
      t match {
        case f @ IFunApp(fun, _) if fun.isInstanceOf[MonoSortedIFunction] &&
          fun.asInstanceOf[MonoSortedIFunction].resSort.isInstanceOf[ADTProxySort] =>
          val sortedFun = fun.asInstanceOf[MonoSortedIFunction]
          val adtSort = sortedFun.resSort.asInstanceOf[ADT.ADTProxySort]
          Some(ADTTerm(f, adtSort))
        case c@IConstant(SortedConstantTerm(_, sort))
          if sort.isInstanceOf[ADTProxySort] =>
          Some(ADTTerm(c, sort.asInstanceOf[ADTProxySort]))
        case _ => None
      }
    }

    override def postVisit(t: IExpression, none : Object,
                           subres: Seq[IExpression]) : IExpression = {
      import IExpression._
      t match {
        case e@Eq(funApp@IFunApp(fun, _), _) if getADTTerm(funApp).nonEmpty =>
          val Eq(newFunApp@IFunApp(_, fieldTerms), newRootTerm) =
            (e update subres).asInstanceOf[IEquation]
          val adtTerm = getADTTerm(newFunApp).get
          val adt = adtTerm.adtSort.adtTheory
          val ctorIndex = adt.constructors.indexOf(fun)
          val selectors = adt.selectors(ctorIndex)
          (for ((fieldTerm, selectorInd) <- fieldTerms zipWithIndex)
            yield selectors(selectorInd)(newRootTerm) ===
              fieldTerm.asInstanceOf[ITerm]).reduce(_ &&& _)
        case t@IFunApp(f,_) =>
          val newApp = t update subres
          (for (theory <- TheoryRegistry lookupSymbol f;
          res <- theory evalFun newApp) yield res) getOrElse newApp
        case _ =>
          t update subres
      }
    }
  }

  // converts "s = S(a, b)" to "f1(s) = a & f2(s) = b"
  private def explodeADTs(expr : IExpression) : IExpression =
    adtTermExploder.visit(expr, null)
}
