/**
 * Copyright (c) 2021-2022 Pontus Ernstedt
 *               2024      Zafer Esen. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package tricera.acsl

import ap.parser.{CollectingVisitor, IAtom, IBinFormula, IBinJunctor, IExpression, IFormula, ITerm}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornClauses.FALSE
import hornconcurrency.ParametricEncoder.System
import hornconcurrency.ParametricEncoder
import tricera.Util.SourceInfo

import scala.collection.{Map, Set}
import tricera.concurrency.CCReader
import tricera.concurrency.CCReader.{CCAssertionClause, CCClause}


// FIXME: Maybe just object? Or create companion?
// FIXME: We should try not to have to pass around the reader object itself,
//        but only necessary data therein.
class Encoder(reader : CCReader) {
  // FIXME: Static, goes in companion object?
  // FIXME: Check if correct construction of false head.
  val falseHead = new IAtom(FALSE, Seq())
  // NOTE: Need to match whatever CCReader uses. Ideally we extract it from
  // there.
  val preSuffix  : String = "_pre"
  val postSuffix : String = "_post"

  // FIXME: Maybe access these via some Context object?
  val system : System = reader.system
  val funsWithAnnot : Set[String] = reader.funsWithAnnot

  val funToPreAtom  : Map[String, IAtom] = reader.funToPreAtom
  val funToPostAtom : Map[String, IAtom] = reader.funToPostAtom
  val funToContract : Map[String, FunctionContract] = reader.funToContract

  val prePredsToReplace  : Set[IExpression.Predicate] = reader.prePredsToReplace
  val postPredsToReplace : Set[IExpression.Predicate] =
    reader.postPredsToReplace

  val hasACSLEntryFunction : Boolean = reader.hasACSLEntryFunction

  val uninterpPreds : Set[IExpression.Predicate] = reader.uninterpPredDecls.values.map(_.pred).toSet

  def encode : System = {
    import ParametricEncoder._
    // NOTE: Order of encoding matters.
    val asserts = encodeAssertions
    val backAxi = encodeBackgroundAxioms
    val processes : ProcessSet =
      if (hasACSLEntryFunction) encodeProcessesEntry else encodeProcesses

    asserts.foreach(cc => reader.mkRichAssertionClause(
      cc.clause, cc.srcInfo, cc.property))

    system.copy(
      assertions = asserts.map(_.clause),
      backgroundAxioms = backAxi match {
        case (Nil, Nil) =>
          ParametricEncoder.NoBackgroundAxioms
        case (preds, clauses) =>
          ParametricEncoder.SomeBackgroundAxioms(preds, clauses.map(_.clause))
      },
      processes = processes
    )
  }
  /**
   *
   * @return encoded assertions and a backmapping from these to the original
   *         clauses
   */
  private def encodeAssertions : Seq[CCAssertionClause] = {
    val (preClauses, others) : (Seq[Clause], Seq[Clause]) = {
      system.assertions.partition(c => {
        prePredsToReplace(c.head.pred)
      })
    }

    val newPreClauses : Seq[CCAssertionClause] =
      preClauses.flatMap(c => buildPreClause(reader.getRichClause(c).get))
    val newPostClauses : Seq[CCAssertionClause] = buildPostAsserts
    others.map(
      c => reader.getRichClause(c).get.asInstanceOf[CCAssertionClause]) ++
    newPreClauses ++ newPostClauses
  }

  // E₁ ∧ ⋯ ∧ E_n ↦ (E₁, …, E_n)
  private def conjuncts(form : IFormula) : Seq[IFormula] = form match {
    case IBinFormula(IBinJunctor.And, l, r) => conjuncts(l) ++ conjuncts(r)
    case _ => form::Nil
  }

  // Make a clause where uninterpreted predicates given in the constraint are instead placed in the body. For example:
  //
  //   Input:  (P₁(⋯),
  //            (P₂(⋯), P₃(⋯), P₄(⋯)),
  //            E₁ ∧ P₅(⋯) ∧ E₂ ∧ P₆(⋯) ∧ E₃)
  //
  //   Output: P₁(⋯) :− P₂(⋯), P₃(⋯), P₄(⋯), P₅(⋯), P₆(⋯), E₁ ∧ E₂ ∧ E₃
  //           i.e.
  //           P₁(⋯) ← P₂(⋯) ∧ P₃(⋯) ∧ P₄(⋯) ∧ P₅(⋯) ∧ P₆(⋯) ∧ E₁ ∧ E₂ ∧ E₃
  //
  private def clauseWUninterpPredsInBody(oldHead : IAtom, oldBody : List[IAtom], oldConstr : IFormula) : Clause = {
    val (newBody, newConstr) : (List[IAtom], Seq[IFormula]) =
      conjuncts(oldConstr)
        .map(elem => elem.asInstanceOf[IFormula])
        .foldRight((oldBody, Nil : List[IFormula]))((cur, acc) =>
          cur match {
            case a@IAtom(pred, _) if uninterpPreds(pred) => (a::acc._1, acc._2)
            case _ => (acc._1, cur::acc._2)
          })
    Clause(oldHead, newBody, IExpression.and(newConstr))
  }

  // Make an assertion and other clauses that together correspond to the assertion consisting of the given body and the conjunction of the first given constraint and the negation of the second given constraint. Uninterpreted predicates given in the second constraint instead become heads. For example:
  //
  //   Input:  ((P₂(⋯), P₃(⋯), P₄(⋯)),
  //            E₄ ∧ E₅,
  //            E₁ ∧ P₅(⋯) ∧ E₂ ∧ P₆(⋯) ∧ E₃)
  //
  //   Output: (⊥ :− P₂(⋯), P₃(⋯), P₄(⋯), (E₄ ∧ E₅) ∧ ¬(E₁ ∧ E₂ ∧ E₃),
  //            P₅ :− P₂(⋯), P₃(⋯), P₄(⋯), (E₄ ∧ E₅),
  //            P₆ :− P₂(⋯), P₃(⋯), P₄(⋯), (E₄ ∧ E₅))
  //           i.e.
  //           P₂(⋯) ∧ P₃(⋯) ∧ P₄(⋯) ∧ E₄ ∧ E₅ → E₁ ∧ P₅(⋯) ∧ E₂ ∧ P₆(⋯) ∧ E₃
  //
  private def assertWNegConstrAndUninterpPredsInHeads(oldBody : List[IAtom], oldConstr : IFormula, oldNegConstr : IFormula) : Seq[Clause] = {
    val (newAssert, newClauses) : (Seq[IFormula], List[Clause]) =
      conjuncts(oldNegConstr)
        .map(elem => elem.asInstanceOf[IFormula])
        .foldRight((Nil : List[IFormula], Nil : List[Clause]))((cur, acc) =>
          cur match {
            case a@IAtom(pred, _) if uninterpPreds(pred) => (acc._1, Clause(a, oldBody, oldConstr)::acc._2)
            case _ => (cur::acc._1, acc._2)
          })
    Clause(falseHead, oldBody, oldConstr &&& IExpression.and(newAssert).unary_!)::newClauses
  }

  /**
   *
   * @return background axioms and a backmapping from these to the original clauses
   */
  private def encodeBackgroundAxioms : (Seq[IExpression.Predicate], Seq[CCClause]) = {
    import ParametricEncoder.{NoBackgroundAxioms, SomeBackgroundAxioms}
    val backmapping = new collection.mutable.HashMap[Clause, Option[Clause]]
    system.backgroundAxioms match {
      case SomeBackgroundAxioms(preds, clauses) => {
        // FIXME: Delete *_pre/*_post predicates relating to annotated
        //        functions from preds?  Not sure what its usage is.
        val encoded = clauses.collect({
          case c@Clause(head, List(atom), _) if prePredsToReplace(atom.pred) => {
            // Handles entry clause, e.g:
            // f0(..) :- f_pre(..) ==> f0(..) :- <pre>
            val name    : String   = atom.pred.name.stripSuffix(preSuffix)
            val preAtom : IAtom    = funToPreAtom(name)
            val preCond : IFormula = funToContract(name).pre
            val constr  : IFormula = applyArgs(preCond, preAtom, atom)
            val clause  : Clause   = clauseWUninterpPredsInBody(head, Nil, constr)
            new CCClause(clause, reader.getRichClause(c).get.srcInfo)::Nil
          }
          case c@Clause(head, body, oldConstr)
            if prePredsToReplace(head.pred) => {
            // Handles recursive calls, e.g:
            // f_pre(..) :- fN(..) ==> false :- fN(..), !<pre>
            buildPreClause(reader.getRichClause(c).get)
          }
          case c@Clause(head, _, _) if !postPredsToReplace(head.pred) =>
            replacePostPredInBody(reader.getRichClause(c).get)::Nil
        }).flatten
        (preds, encoded)
      }
      case NoBackgroundAxioms => (Nil, Nil)
    }
  }

  private def encodeProcessesEntry : ParametricEncoder.ProcessSet = {
    system.processes.map({
      case (p, r) =>
        val updated = p.collect({
          case (Clause(head, List(atom), _), sync)
            if prePredsToReplace(atom.pred) => {
            // Handles entry clause, e.g:
            // f0(..) :- f_pre(..) ==> f0(..) :- <pre>
            val name    : String   = atom.pred.name.stripSuffix(preSuffix)
            val preAtom : IAtom    = funToPreAtom(name)
            val preCond : IFormula = funToContract(name).pre
            val constr  : IFormula = applyArgs(preCond, preAtom, atom)
            (Clause(head, List(), constr), sync)
          }
          case (c@Clause(head, _, _), sync) if !(postPredsToReplace(head.pred)
                                            || prePredsToReplace(head.pred)) =>
            // Keep all other clauses besides those which we generate assertions for.
              (replacePostPredInBody(reader.getRichClause(c).get).clause, sync) // todo: fix
        })
        for((clause, _) <- updated) {
          reader.addRichClause(clause, None) // todo: add line numbers
        }
        (updated, r)
    })
  }

  private def encodeProcesses : ParametricEncoder.ProcessSet = {
    system.processes.map({
      case (p, r) =>
        val (clauses, syncs) = p.unzip
        val newClauses : Seq[CCClause] = clauses.map(
          c => replacePostPredInBody(reader.getRichClause(c).get))
        newClauses.foreach(cc => reader.addRichClause(cc.clause, cc.srcInfo))
        (newClauses.map(_.clause).zip(syncs), r) // todo: fix
    })
  }

  private def replacePostPredInBody(c : CCClause) : CCClause = c match {
    // Handles assumption of postcondition after call, e.g:
    // mainN+1(..) :- mainN(..), f_post(..) ==>
    // mainN+1(..) :- mainN(..), <post> & <assigns>
    case CCClause(Clause(head, body, constr), oldSrcInfo) =>
      val (toss, keep) = body.partition(a => postPredsToReplace(a.pred))
      val (maybeNewConstr, newSrcInfo) = toss match {
        case atom :: Nil =>
          val name : String = atom.pred.name.stripSuffix(postSuffix)
          val postAtom : IAtom = funToPostAtom(name)
          val postCond : IFormula = funToContract(name).post
          val assigns  : IFormula = funToContract(name).assignsAssume
          (constr &&& applyArgs(postCond &&& assigns, postAtom, atom),
            Some(funToContract(name).postSrcInfo)
          )
        case _ => (constr, oldSrcInfo)
      }
      new CCClause(Clause(head, keep, maybeNewConstr), newSrcInfo)
  }

  // Handles function calls, e.g:
  // f_pre(..) :- mainN(..), .. ==> false :- mainN(..), .., !<pre>
  private def buildPreClause(old : CCClause) : Seq[CCAssertionClause] = {
    assert(prePredsToReplace(old.clause.head.pred))
    val name    : String   = old.clause.head.pred.name.stripSuffix(preSuffix)
    val preAtom : IAtom    = funToPreAtom(name)
    val preCond : IFormula = funToContract(name).pre
    val constr  : IFormula = applyArgs(preCond, preAtom, old.clause.head)
    for (clause <- assertWNegConstrAndUninterpPredsInHeads(old.clause.body, IExpression i true, constr))
      yield reader.mkRichAssertionClause(clause,
                                         old.srcInfo,
                                         tricera.properties.FunctionPrecondition(name, old.srcInfo))
  }

  // Fetches clauses from system.processes and system.backgroundAxioms implying
  // post-condition and generates assertion clauses (to be moved into
  // system.assertions).
  private def buildPostAsserts : Seq[CCAssertionClause] = {
    import ParametricEncoder.{NoBackgroundAxioms, SomeBackgroundAxioms}
    val clauses1 : Seq[CCClause] =
      system.processes.flatMap({
        case (p, r) => p.map(p => reader.getRichClause(p._1).get)
      })
    val clauses2 : Seq[CCClause] =
      system.backgroundAxioms match {
        case SomeBackgroundAxioms(preds, clauses) => clauses.map(c => reader.getRichClause(c).get)
        case NoBackgroundAxioms => Seq()
      }

    val clauses : Seq[CCClause] = clauses1 ++ clauses2

    clauses.collect({
      // Handles final clause, e.g:
      // f_post(..) :- f1(..) ==> false :- f1(..), !(<post> & <assigns>)
      case CCClause(Clause(head, oldBody, oldConstr), srcInfo)
        if postPredsToReplace(head.pred) =>
        val name     : String     = head.pred.name.stripSuffix(postSuffix)
        val postAtom : IAtom      = funToPostAtom(name)
        val postCond : IFormula   = funToContract(name).post
        val postSrc  : SourceInfo = funToContract(name).postSrcInfo
        val constr   : IFormula   = applyArgs(postCond, postAtom, head)
        val assigns  : IFormula   =
          applyArgs(funToContract(name).assignsAssert, postAtom, head)
        for (clause <- assertWNegConstrAndUninterpPredsInHeads(oldBody, oldConstr, constr &&& assigns))
          yield reader.mkRichAssertionClause(clause,
                                             Some(postSrc),
                                             tricera.properties.FunctionPostcondition(name, srcInfo))
    }).flatten
  }

  private def applyArgs(formula : IFormula, predParams : IAtom, predArgs : IAtom) : IFormula = {
    val paramToArgMap : Map[ITerm, ITerm] =
      predParams.args.zip(predArgs.args).toMap
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
          // NOTE: Check fixes so that expressions as args works (e.g foo(2+2)).
          if (subres.isEmpty) exp else exp.update(subres)
        case exp =>
          exp.update(subres)
      }
    }
  }
}
