/**
 * Copyright (c) 2026 Zafer Esen. All rights reserved.
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

package tricera.postprocessor

import ap.parser._
import ap.parser.IExpression._
import lazabs.GlobalParameters
import lazabs.horn.bottomup.SimpleWrapper
import lazabs.horn.bottomup.HornClauses.Clause
import tricera._
import tricera.acsl.{ACSLTranslator, FunctionContract}
import tricera.concurrency.CCReader
import tricera.concurrency.ccreader.CCPredicate
import tricera.params.TriCeraParameters

import scala.util.control.NonFatal

/** Check that a function satisfies its printed contract for all inputs allowed
 *  by requires, including valid memory accesses and frees. */
class ACSLContractVerifier(original : CCReader) {
  // the original encoding may omit memory checks; build them in a separate reader
  // once, when the first contract is checked
  private lazy val reader = Console.withOut(lazabs.horn.Util.NullStream) {
    Console.withErr(lazabs.horn.Util.NullStream) {
      original.reencode(Set(properties.MemValidDeref, properties.MemValidFree))
    }
  }
  private lazy val contexts = reader.getFunctionContexts
  private val verifiedContracts = scala.collection.mutable.Map[String, FunctionContract]()
  private val preOwners = original.getFunctionContexts.map { case (name, c) => c.prePred.pred -> name }

  // a call to g produces a clause with g_pre in its head
  def callees(id : String) : Seq[String] =
    original.getContractVerificationClauses(id).toSeq.flatten.iterator
      .flatMap(c => preOwners.get(c.head.pred)).filterNot(_ == id)
      .toSeq.distinct.sorted

  private def instantiate(form : IFormula, pred : CCPredicate,
                          atom : IAtom) : IFormula =
    ConstantSubstVisitor(form, pred.argVars.map(_.term).zip(atom.args).toMap)

  private object CheckTimeout extends RuntimeException

  // check the printed ACSL, since translation may have dropped requirements
  def verify(printed : ACSLLinearisedContract, timeoutMillis : Long = 1000L) : Boolean = {
    val id = printed.funcName
    if (original.getContractVerificationClauses(id).isEmpty) return false
    val params = GlobalParameters.get.clone
    val outerCheck = params.timeoutChecker
    val deadline = System.nanoTime() + timeoutMillis * 1000000L
    // stop a slow contract check without using up the whole program timeout
    params.timeoutChecker = () => {
      outerCheck()
      if (System.nanoTime() >= deadline) throw CheckTimeout
    }
    try {
      val proved = GlobalParameters.withValue(params) {
        val assigns = printed.assigns.map(a => s"assigns $a;").getOrElse("")
        val contract = Console.withOut(lazabs.horn.Util.NullStream) {
          Console.withErr(lazabs.horn.Util.NullStream) {
            ACSLTranslator.translateACSL(
              s"/*@ requires ${printed.preCondition}; ensures ${printed.postCondition}; $assigns */",
              contexts(id).acslContext).asInstanceOf[FunctionContract]
          }
        }
        params.timeoutChecker()
        val safe = verifyBody(id, contract).contains(true)
        params.timeoutChecker()
        if (safe) verifiedContracts(id) = contract
        safe
      }
      outerCheck()
      proved
    } catch {
      case e @ (tricera.Main.StoppedException | tricera.Main.TimeoutException) => throw e
      case NonFatal(e) =>
        Util.printlnDebug("ACSL contract check skipped " + id + ": " + e.toString)
        false
    }
  }

  private def verifyBody(id : String, contract : FunctionContract) : Option[Boolean] = {
    // include callees unless their contracts have already passed this checker
    // the original solution need not prove memory safety
    val included = scala.collection.mutable.LinkedHashSet[String]()
    def include(name : String) : Unit =
      if (included.add(name))
        callees(name).filterNot(verifiedContracts.contains).foreach(include)
    include(id)
    val clauses = included.toSeq.flatMap(reader.getContractVerificationClauses(_).toSeq.flatten)
    // replace pre/post predicates with contracts; other predicates remain unknown
    val boundaries = contexts.toSeq.flatMap { case (name, c) =>
      val known = if (name == id) Some(contract)
                  else verifiedContracts.get(name).orElse(reader.funToContract.get(name))
      known.toSeq.flatMap { annotated => Seq(
        c.prePred.pred -> (c.prePred, annotated.pre &&& c.globalArrayPrecondition),
        c.postPred.pred -> (c.postPred, annotated.post &&& annotated.assignsAssume &&&
                                      c.globalArrayPostcondition)) }
    }.toMap
    val localPredicates = clauses.map(_.head.pred).toSet
    require(clauses.flatMap(_.body).forall(a =>
      localPredicates(a.pred) || boundaries.contains(a.pred)),
      "missing callee contract")

    // f_entry :- f_pre becomes f_entry :- requires
    // f_post :- f_exit becomes false :- f_exit, !ensures
    // here ensures includes assigns and the facts about global array storage
    // Calls to verified contracts assert requires and assume ensures
    // Other callee preds stay in the clauses for inference
    val checks = clauses.map { clause =>
      val (replaced, body) = clause.body.partition(a => boundaries.contains(a.pred))
      val constraint = clause.constraint &&& and(replaced.map { a =>
        val (pred, form) = boundaries(a.pred)
        instantiate(form, pred, a)
      })
      boundaries.get(clause.head.pred) match {
        case Some((pred, form)) =>
          Clause(SimpleWrapper.FALSEAtom, body,
            constraint &&& !instantiate(form, pred, clause.head))
        case None => Clause(clause.head, body, constraint)
      }
    }
    val safe = SimpleWrapper.isSat(checks,
      useTemplates = TriCeraParameters.get.templateBasedInterpolation)
    if (GlobalParameters.get.didIncompleteTransformation) None else Some(safe)
  }

}
