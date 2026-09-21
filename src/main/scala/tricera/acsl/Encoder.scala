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

import ap.parser.IExpression
import ap.parser.CollectingVisitor
import ap.parser.{IAtom, IFormula, ITerm}
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
  import tricera.Literals.{predPostSuffix, predPreSuffix}
  // FIXME: Static, goes in companion object?
  // FIXME: Check if correct construction of false head.
  val falseHead = new IAtom(FALSE, Seq())

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

  def encode : System = {
    import ParametricEncoder._
    // NOTE: Order of encoding matters.
    val asserts = encodeAssertions
    val backAxi = encodeBackgroundAxioms
    val processes : ProcessSet =
      if (hasACSLEntryFunction) encodeProcessesEntry else system.processes

    system.copy(
      assertions = asserts.map(replacePostPredInBody),
      backgroundAxioms = backAxi match {
        case (Nil, Nil) =>
          ParametricEncoder.NoBackgroundAxioms
        case (preds, clauses) =>
          ParametricEncoder.SomeBackgroundAxioms(preds, clauses.map(replacePostPredInBody))
      },
      processes = processes.map { case (clauses, replication) =>
        (clauses.map { case (clause, sync) =>
          (replacePostPredInBody(reader.getRichClause(clause).get), sync)
        }, replication)
      }
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
      preClauses.flatMap(c => buildPreClauses(reader.getRichClause(c).get))
    val newPostClauses : Seq[CCAssertionClause] = buildPostAsserts
    others.map(
      c => reader.getRichClause(c).get.asInstanceOf[CCAssertionClause]) ++
    newPreClauses ++ newPostClauses
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
        val encoded = clauses.collect({
          case c@Clause(head, List(atom), _) if prePredsToReplace(atom.pred) => {
            // Handles entry clause, e.g:
            // f0(..) :- f_pre(..) ==> f0(..) :- <pre>
            val name    : String   = atom.pred.name.stripSuffix(predPreSuffix)
            val preAtom : IAtom    = funToPreAtom(name)
            val preCond : IFormula = funToContract(name).pre &&&
              reader.getFunctionContexts(name).globalArrayPrecondition
            val constr  : IFormula = applyArgs(preCond, preAtom, atom)
            new CCClause(Clause(head, List(), constr),
                         reader.getRichClause(c).get.srcInfo)
          }
          case c@Clause(head, body, oldConstr)
            if prePredsToReplace(head.pred) => {
            // Handles recursive calls, e.g:
            // f_pre(..) :- fN(..) ==> false :- fN(..), !<pre>
            buildPreClause(reader.getRichClause(c).get)
          }
          case c@Clause(head, _, _) if !postPredsToReplace(head.pred) =>
            reader.getRichClause(c).get
        })
        // remove preds replaced by contracts
        val remainingPreds = preds.filterNot(p =>
          prePredsToReplace(p) || postPredsToReplace(p))
        (remainingPreds, encoded)
      }
      case NoBackgroundAxioms => (Nil, Nil)
    }
  }

  private def encodeProcessesEntry : ParametricEncoder.ProcessSet = {
    system.processes.map({
      case (p, r) =>
        val updated = p.collect({
          case (c@Clause(head, List(atom), _), sync)
            if prePredsToReplace(atom.pred) => {
            // Handles entry clause, e.g:
            // f0(..) :- f_pre(..) ==> f0(..) :- <pre>
            val name    : String   = atom.pred.name.stripSuffix(predPreSuffix)
            val preAtom : IAtom    = funToPreAtom(name)
            val preCond : IFormula = funToContract(name).pre &&&
              reader.getFunctionContexts(name).globalArrayPrecondition
            val constr  : IFormula = applyArgs(preCond, preAtom, atom)
            (reader.addRichClause(Clause(head, List(), constr),
              reader.getRichClause(c).get.srcInfo).clause, sync)
          }
          case (c@Clause(head, _, _), sync) if !(postPredsToReplace(head.pred)
                                            || prePredsToReplace(head.pred)) =>
            // Keep all other clauses besides those which we generate assertions for.
              (c, sync)
        })
        (updated, r)
    })
  }

  private def replacePostPredInBody(c : CCClause) : Clause = c match {
    // After checking the precondition, assume it along with the postcondition.
    // mainN+1(..) :- mainN(..), f_post(..) ==>
    // mainN+1(..) :- mainN(..), <pre> & <post> & <assigns>
    case CCClause(Clause(head, body, constr), oldSrcInfo) =>
      val (toss, keep) = body.partition(a => postPredsToReplace(a.pred))
      // nested calls can cause several post preds
      val postconditions = toss.map { atom =>
        val name = atom.pred.name.stripSuffix(predPostSuffix)
        val contract = funToContract(name)
        applyArgs(contract.pre &&& contract.post &&& contract.assignsAssume &&&
          reader.getFunctionContexts(name).globalArrayPostcondition,
          funToPostAtom(name), atom)
      }
      val newSrcInfo = toss match {
        case atom :: Nil => Some(funToContract(
          atom.pred.name.stripSuffix(predPostSuffix)).postSrcInfo)
        case _ => oldSrcInfo
      }
      val clause = Clause(head, keep, constr &&& IExpression.and(postconditions))
      c match {
        // Keep the assertion's location and property for error reporting.
        case a : CCAssertionClause =>
          reader.mkRichAssertionClause(clause, a.srcInfo, a.property)
        case _ => reader.addRichClause(clause, newSrcInfo)
      }
      clause
  }

  // Handles function calls, e.g:
  // f_pre(..) :- mainN(..), .. ==> false :- mainN(..), .., !<pre>
  private def buildPreClause(old : CCClause) : CCAssertionClause = {
    assert(prePredsToReplace(old.clause.head.pred))
    val name    : String   = old.clause.head.pred.name.stripSuffix(predPreSuffix)
    val preCond : IFormula = funToContract(name).pre
    val preAtom : IAtom    = funToPreAtom(name)
    val constr  : IFormula = old.clause.constraint &&&
      applyArgs(preCond, preAtom, old.clause.head).unary_!
    reader.mkRichAssertionClause(Clause(falseHead, old.clause.body, constr),
                              old.srcInfo,
                              tricera.properties.FunctionPrecondition(name, old.srcInfo))
  }

  private def buildPreClauses(old : CCClause) : Seq[CCAssertionClause] = {
    assert(prePredsToReplace(old.clause.head.pred))
    val name     : String = old.clause.head.pred.name.stripSuffix(predPreSuffix)
    val preAtom  : IAtom  = funToPreAtom(name)
    val contract = funToContract(name)
    val (named, unnamed) = contract.preClauses.partition(_._1.isDefined)
    val namedAsserts = named.map { case (clauseName, f) =>
      reader.mkRichAssertionClause(
        Clause(falseHead, old.clause.body,
               old.clause.constraint &&& applyArgs(f, preAtom, old.clause.head).unary_!),
        old.srcInfo,
        tricera.properties.FunctionPrecondition(name, old.srcInfo, clauseName))
    }
    val unnamedPre : IFormula = IExpression.and(unnamed.map(_._2))
    val rest = reader.mkRichAssertionClause(
      Clause(falseHead, old.clause.body,
             old.clause.constraint &&& applyArgs(unnamedPre, preAtom, old.clause.head).unary_!),
      old.srcInfo,
      tricera.properties.FunctionPrecondition(name, old.srcInfo))
    namedAsserts :+ rest
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

    clauses.flatMap({
      // Handles final clause, e.g:
      // f_post(..) :- f1(..) ==> false :- f1(..), !(<post> & <assigns>)
      case CCClause(Clause(head, body, oldConstr), srcInfo)
        if postPredsToReplace(head.pred) =>
        val name     : String   = head.pred.name.stripSuffix(predPostSuffix)
        val postAtom : IAtom    = funToPostAtom(name)
        val contract = funToContract(name)
        val postSrc  : SourceInfo = contract.postSrcInfo
        val assigns  : IFormula =
          applyArgs(contract.assignsAssert, postAtom, head)
        val (named, unnamed) = contract.postClauses.partition(_._1.isDefined)
        val namedAsserts = named.map { case (clauseName, f) =>
          reader.mkRichAssertionClause(Clause(
            falseHead, body, oldConstr &&& applyArgs(f, postAtom, head).unary_!),
            Some(postSrc),
            tricera.properties.FunctionPostcondition(name, srcInfo, clauseName))
        }
        val unnamedPost : IFormula =
          applyArgs(IExpression.and(unnamed.map(_._2)), postAtom, head)
        val rest = reader.mkRichAssertionClause(Clause(
          falseHead, body, oldConstr &&& (unnamedPost &&& assigns).unary_!),
          Some(postSrc),
          tricera.properties.FunctionPostcondition(name, srcInfo))
        namedAsserts :+ rest
      case _ => Seq()
    })
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
