package tricera.acsl

import ap.parser.IExpression
import ap.parser.CollectingVisitor
import ap.parser.{ITerm, IFormula, IAtom}

import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornClauses.FALSE
import hornconcurrency.ParametricEncoder.System
import hornconcurrency.ParametricEncoder

import scala.collection.{Map, Set}

import tricera.concurrency.CCReader

// FIXME: Maybe just object? Or create companion?
// FIXME: We should try not to have to pass around the reader object itself,
//        but only necessary data therein.
class Encoder(reader : CCReader) {
  // FIXME: Static, goes in companion object?
  // FIXME: Check if correct construction of false head.
  val falseHead = new IAtom(FALSE, Seq())
  val suffix : String = "_pre"

  // FIXME: Maybe access these via some Context object?
  val system = reader.system
  val funsWithAnnot : Set[String] = reader.funsWithAnnot
  val funToPreAtom  : Map[String, IAtom] = reader.funToPreAtom
  val funToPostAtom : Map[String, IAtom] = reader.funToPostAtom
  val funToContract : Map[String, FunctionContract] = reader.funToContract
  val prePredsToReplace : Set[IExpression.Predicate] = reader.prePredsToReplace

  def encode : System = {
    val asserts = encodeAssertions
    val backAxi = encodeBackgroundAxioms
    system.copy(assertions = asserts, backgroundAxioms = backAxi)
  }

  private def buildPreClause(old : Clause) : Clause = {
    assert(old.head.pred.name.endsWith(suffix))
    val body : List[IAtom] = old.body
    val funName : String = old.head.pred.name.stripSuffix(suffix)
    val oldPre : IFormula = funToContract(funName).pre
    val constraint : IFormula = replaceParams(oldPre, funName, old.head).unary_!
    new Clause(falseHead, old.body, constraint)
  }

  private def replaceParams(formula : IFormula, funName : String, pred : IAtom) : IFormula = {
    val preAtom  = funToPreAtom(funName)
    val paramToArgMap = preAtom.args.zip(pred.args).toMap
    ArgSubstVisitor(formula, paramToArgMap)
  }

  private def buildPostClause(name : String) : Clause = {
    new Clause(falseHead, List(funToPostAtom(name)), funToContract(name).post.unary_!)
  }

  private def encodeAssertions : Seq[Clause] = {
    val (preClauses, others) : (Seq[Clause], Seq[Clause]) = 
      system.assertions.partition(c => {
        prePredsToReplace(c.head.pred)
      })
    val newPreClauses : Seq[Clause] = preClauses.map(buildPreClause)
    val newPostClauses : Seq[Clause] = funsWithAnnot.map(buildPostClause).toSeq
    
    newPreClauses ++ newPostClauses ++ others
  }

  private def encodeBackgroundAxioms : ParametricEncoder.BackgroundAxioms = {
    import ParametricEncoder.{NoBackgroundAxioms, SomeBackgroundAxioms}
    system.backgroundAxioms match {
      case SomeBackgroundAxioms(preds, clauses) => {
        // TODO: Delete *_pre predicates relating to annotated functions from preds?
        val encoded = clauses.map({
          case Clause(head, List(atom), _) if prePredsToReplace(atom.pred) => {
            val name    : String   = atom.pred.name.stripSuffix(suffix)
            val preAtom : IAtom    = funToPreAtom(name)
            val preCond : IFormula = funToContract(name).pre
            val paramToArgMap : Map[ITerm, ITerm] = preAtom.args.zip(atom.args).toMap
            new Clause(head, List(), ArgSubstVisitor(preCond, paramToArgMap))
          }
          case c => c
        })
        SomeBackgroundAxioms(preds, encoded)
      }
      case NoBackgroundAxioms => NoBackgroundAxioms
    }
  }


  object ArgSubstVisitor extends CollectingVisitor[Map[ITerm, ITerm], IExpression] {
    def apply(e : IFormula, paramToArgMap : Map[ITerm, ITerm]) : IFormula = {
      visit(e, paramToArgMap).asInstanceOf[IFormula]
    }

    override def postVisit(e: IExpression, paramToArgMap : Map[ITerm, ITerm], subres: Seq[IExpression]) : IExpression = {
      e match {
        case t : ITerm => 
          val exp = paramToArgMap.getOrElse(t, t)//.update(subres)
          // NOTE: Seems to fix so that expressions as args works (e.g. foo(2+2)).
          //       Unsure why.
          if (subres.isEmpty) exp else exp.update(subres)
        case exp =>
          exp.update(subres)
      }
    }
  }
}
