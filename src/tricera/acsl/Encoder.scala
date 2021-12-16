package tricera.acsl

import ap.parser.IExpression
import ap.parser.CollectingVisitor
import ap.parser.{ITerm, IFormula, IAtom}

import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornClauses.FALSE
import hornconcurrency.ParametricEncoder.System
import hornconcurrency.ParametricEncoder

import scala.collection.Map

import tricera.concurrency.CCReader.{CCVar}
import tricera.concurrency.CCReader

// FIXME: Maybe just object?
class Encoder(reader : CCReader, contracts : Map[String, FunctionContract]) {
  // FIXME: Check if correct construction of false head.
  val falseHead = new IAtom(FALSE, Seq())
  val system = reader.system
  // FIXME: Not allowed, but maybe would be convenient.
  //val preds = reader.getFunctionContracts
  val suffix : String = "_pre"

  def encode : System = {
    val asserts = encodeAssertions
    val backAxi = encodeBackgroundAxioms
    system.copy(assertions = asserts, backgroundAxioms = backAxi)
  }

  private def buildPreClause(old : Clause) : Clause = {
    assert(old.head.pred.name.endsWith(suffix))
    val body : List[IAtom] = old.body
    val funName : String = old.head.pred.name.stripSuffix(suffix)
    val oldPre : IFormula = contracts.get(funName)
      .getOrElse(throw new Exception(funName + "not found in map.")).pre
    val constraint : IFormula = replaceParams(oldPre, funName, old.head).unary_!
    new Clause(falseHead, old.body, constraint)
  }

  private def replaceParams(formula : IFormula, funName : String, pred : IAtom) : IFormula = {
    val (pre, post) = reader.getFunctionContracts(funName)
    val preArgs : Seq[ITerm] = pre.argVars.map(_.term)
    val paramToArgMap : Map[ITerm, ITerm] = preArgs.zip(pred.args).toMap
    ArgSubstVisitor(formula, paramToArgMap)
  }

  private def buildPostClauses : Seq[Clause] = {
    for ((name, (_, post)) <- reader.getFunctionContracts.toSeq
         if reader.functionsWithAnnot(name))
      yield new Clause(falseHead, List(new IAtom(post.pred, post.argVars.map(_.term))), contracts(name).post.unary_!)
  }

  private def encodeAssertions : Seq[Clause] = {
    val (preClauses, others) : (Seq[Clause], Seq[Clause]) = 
      system.assertions.partition(c => {
        val name = c.head.pred.name
        name.endsWith(suffix) && reader.functionsWithAnnot(name.stripSuffix(suffix))
      })
    val newPreClauses : Seq[Clause] = preClauses.map(buildPreClause)
    val newPostClauses : Seq[Clause] = buildPostClauses 
    
    newPreClauses ++ newPostClauses ++ others
  }

  // FIXME: Honestly no idea what type this returns.
  //        Not Option[Seq[ITerm] => IFormula]..
  //        Where does ParametricEncoder.SomeBackgroundAxioms come from?
  private def encodeBackgroundAxioms = {
    system.backgroundAxioms match {
      case ParametricEncoder.SomeBackgroundAxioms(preds, clauses) => {
        // TODO: Delete *_pre predicates from preds?
        val (preConds, others) = 
          clauses.partition(
            _.body match {
              case atom :: Nil => 
                val name = atom.pred.name
                name.endsWith(suffix) && reader.functionsWithAnnot(name.stripSuffix(suffix))
              case _ => false
            }
          )
        val updated = preConds.map(c => 
            new Clause(c.head, List(), contracts(c.body(0).pred.name.stripSuffix(suffix)).pre)
        )
        ParametricEncoder.SomeBackgroundAxioms(preds, updated ++ others)
      }
      case ParametricEncoder.NoBackgroundAxioms => 
        ParametricEncoder.NoBackgroundAxioms
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
