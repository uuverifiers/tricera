package tricera.concurrency.ccreader

import ap.parser.IExpression._
import ap.parser.{IAtom, ITerm}
import tricera.Util.SourceInfo

// a wrapper for IExpression.Predicate that keeps more info about arguments
case class CCPredicate(pred : Predicate, argVars : scala.Seq[CCVar],
                       srcInfo : Option[SourceInfo]) {


  def apply(terms : scala.Seq[ITerm]) : IAtom =
    pred(terms: _*)
  def apply[X: scala.reflect.ClassTag](ccVars : scala.Seq[CCVar]) : IAtom =
    pred(ccVars.map(_.term): _*)
  def arity : Int = pred.arity
  override def toString: String =
    pred.name + (if(argVars.nonEmpty) "(" + argVars.mkString(", ") + ")" else "")
  def toStringWithLineNumbers: String =
    pred.name + (if(argVars.nonEmpty) "(" +
      argVars.map(_.toStringWithLineNumbers).mkString(", ") + ")" else "")
  assert(pred.arity == argVars.size)
}
