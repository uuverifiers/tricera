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
  // NOTE: Need to match whatever CCReader uses. Ideally we extract it from there.
  val preSuffix  : String = "_pre"
  val postSuffix : String = "_post"

  // FIXME: Maybe access these via some Context object?
  val system : System = reader.system
  val funsWithAnnot : Set[String] = reader.funsWithAnnot

  val funToPreAtom  : Map[String, IAtom] = reader.funToPreAtom
  val funToPostAtom : Map[String, IAtom] = reader.funToPostAtom
  val funToContract : Map[String, FunctionContract] = reader.funToContract

  val prePredsToReplace  : Set[IExpression.Predicate] = reader.prePredsToReplace
  val postPredsToReplace : Set[IExpression.Predicate] = reader.postPredsToReplace
  
  val hasACSLEntryFunction : Boolean = reader.hasACSLEntryFunction

  def encode : System = {
    import ParametricEncoder._
    // NOTE: Order of encoding matters.
    val asserts   : Seq[Clause]      = encodeAssertions
    val backAxi   : BackgroundAxioms = encodeBackgroundAxioms
    val processes : ProcessSet = 
      if (hasACSLEntryFunction) encodeProcessesEntry else encodeProcesses
    system.copy(
      assertions = asserts,
      backgroundAxioms = backAxi,
      processes = processes
    )
  }

  private def encodeAssertions : Seq[Clause] = {
    val (preClauses, others) : (Seq[Clause], Seq[Clause]) = 
      system.assertions.partition(c => {
        prePredsToReplace(c.head.pred)
      })

    val newPreClauses : Seq[Clause] = preClauses.map(buildPreClause)
    val newPostClauses : Seq[Clause] =
      if (hasACSLEntryFunction) buildPostAsserts else Seq()
    others ++ newPreClauses ++ newPostClauses
  }

  private def encodeBackgroundAxioms : ParametricEncoder.BackgroundAxioms = {
    import ParametricEncoder.{NoBackgroundAxioms, SomeBackgroundAxioms}
    system.backgroundAxioms match {
      case SomeBackgroundAxioms(preds, clauses) => {
        // FIXME: Delete *_pre/*_post predicates relating to annotated functions from preds?
        //        Not sure what its usage is.
        val encoded = clauses.map({
          case Clause(head, List(atom), _) if prePredsToReplace(atom.pred) => {
            // Handles entry clause, e.g: 
            // f0(..) :- f_pre(..) ==> f0(..) :- <pre>
            val name    : String   = atom.pred.name.stripSuffix(preSuffix)
            val preAtom : IAtom    = funToPreAtom(name)
            val preCond : IFormula = funToContract(name).pre
            val constr  : IFormula = applyArgs(preCond, preAtom, atom)
            Clause(head, List(), constr)
          }
          case c@Clause(head, body, oldConstr) if prePredsToReplace(head.pred) => {
            // Handles recursive calls, e.g:
            // f_pre(..) :- fN(..) ==> false :- fN(..), !<pre>
            buildPreClause(c)
          }
          case Clause(head, body, oldConstr) if postPredsToReplace(head.pred) => {
            // Handles final clause, e.g:
            // f_post(..) :- f1(..) ==> false :- f1(..), !(<post> & <assigns>)
            val name     : String   = head.pred.name.stripSuffix(postSuffix)
            val postAtom : IAtom    = funToPostAtom(name)
            val postCond : IFormula = funToContract(name).post
            val constr   : IFormula = applyArgs(postCond, postAtom, head)
            val assigns  : IFormula = applyArgs(funToContract(name).assigns, postAtom, head)
            Clause(falseHead, body, oldConstr &&& (constr &&& assigns).unary_!)
          }
          case c => replacePostPredInBody(c)
        })
        SomeBackgroundAxioms(preds, encoded)
      }
      case NoBackgroundAxioms => NoBackgroundAxioms
    }
  }

  private def encodeProcessesEntry : ParametricEncoder.ProcessSet = {
    system.processes.map({
      case (p, r) =>
        val updated = p.collect({
          case (Clause(head, List(atom), _), sync) if prePredsToReplace(atom.pred) => {
            // Handles entry clause, e.g: 
            // f0(..) :- f_pre(..) ==> f0(..) :- <pre>
            val name    : String   = atom.pred.name.stripSuffix(preSuffix)
            val preAtom : IAtom    = funToPreAtom(name)
            val preCond : IFormula = funToContract(name).pre
            val constr  : IFormula = applyArgs(preCond, preAtom, atom)
            (Clause(head, List(), constr), sync)
          }
          case (c@Clause(head, _, _), sync)
            // Keep all other clauses besides those which we generate assertions for.
            if !(postPredsToReplace(head.pred) || prePredsToReplace(head.pred)) =>
              (replacePostPredInBody(c), sync)
        })
        (updated, r)
    })
  }

  private def encodeProcesses : ParametricEncoder.ProcessSet = {
    system.processes.map({
      case (p, r) =>
        val (clauses, syncs) = p.unzip
        val newClauses : Seq[Clause] = clauses.map(replacePostPredInBody)
        (newClauses.zip(syncs), r)
    })
  }

  private def replacePostPredInBody(c : Clause) : Clause = c match {
    // Handles assumption of postcondition after call, e.g:
    // mainN+1(..) :- mainN(..), f_post(..) ==>
    // mainN+1(..) :- mainN(..), <post> & <assigns>
    case Clause(head, body, constr) =>
      val (toss, keep) = body.partition(a => postPredsToReplace(a.pred))
      val maybeNewConstr = toss match {
        case atom :: Nil =>
          val name : String = atom.pred.name.stripSuffix(postSuffix)
          val postAtom : IAtom = funToPostAtom(name)
          val postCond : IFormula = funToContract(name).post
          val assigns  : IFormula = funToContract(name).assigns
          constr &&& applyArgs(postCond &&& assigns, postAtom, atom)
        case _ => constr
      }
      Clause(head, keep, maybeNewConstr)
  }

  // Handles function calls, e.g:
  // f_pre(..) :- mainN(..), .. ==> false :- mainN(..), .., !<pre>
  private def buildPreClause(old : Clause) : Clause = {
    assert(prePredsToReplace(old.head.pred))
    val name    : String   = old.head.pred.name.stripSuffix(preSuffix)
    val preCond : IFormula = funToContract(name).pre
    val preAtom : IAtom    = funToPreAtom(name)
    val constr  : IFormula = applyArgs(preCond, preAtom, old.head).unary_!
    new Clause(falseHead, old.body, constr)
  }

  // Fetches clauses from system.processes implying pre/postcondition and generates
  // assertion clauses (to be moved into system.assertions).
  private def buildPostAsserts : Seq[Clause] = {
    system.processes.flatMap({
      case (p, r) =>
        val (clauses, _) = p.unzip
        clauses.collect({
          case Clause(head, body, oldConstr) if prePredsToReplace(head.pred) => {
            val name     : String   = head.pred.name.stripSuffix(preSuffix)
            val preAtom  : IAtom    = funToPreAtom(name)
            val preCond  : IFormula = funToContract(name).pre
            val constr   : IFormula = applyArgs(preCond, preAtom, head).unary_!
            Clause(falseHead, body, oldConstr &&& constr)
          }
          case Clause(head, body, oldConstr) if postPredsToReplace(head.pred) => {
            val name     : String   = head.pred.name.stripSuffix(postSuffix)
            val postAtom : IAtom    = funToPostAtom(name)
            val postCond : IFormula = funToContract(name).post
            val constr   : IFormula = applyArgs(postCond, postAtom, head)
            val assigns  : IFormula = applyArgs(funToContract(name).assigns, postAtom, head)
            Clause(falseHead, body, oldConstr &&& (constr &&& assigns).unary_!)
          }
        })
    })
  }


  private def applyArgs(formula : IFormula, predParams : IAtom, predArgs : IAtom) : IFormula = {
    val paramToArgMap : Map[ITerm, ITerm] = predParams.args.zip(predArgs.args).toMap
    TermSubstVisitor(formula, paramToArgMap)
  }

  object TermSubstVisitor extends CollectingVisitor[Map[ITerm, ITerm], IExpression] {
    def apply(e : IFormula, paramToArgMap : Map[ITerm, ITerm]) : IFormula = {
      visit(e, paramToArgMap).asInstanceOf[IFormula]
    }

    override def postVisit(e: IExpression, paramToArgMap : Map[ITerm, ITerm], subres: Seq[IExpression]) : IExpression = {
      e match {
        case t : ITerm => 
          val exp = paramToArgMap.getOrElse(t, t)
          // NOTE: Check fixes so that expressions as args works (e.g. foo(2+2)).
          if (subres.isEmpty) exp else exp.update(subres)
        case exp =>
          exp.update(subres)
      }
    }
  }
}
