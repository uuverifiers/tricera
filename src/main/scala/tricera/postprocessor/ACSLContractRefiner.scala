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

import ap.SimpleAPI
import ap.parser._
import ap.parser.IExpression._
import ap.theories.TheoryCollector
import lazabs.GlobalParameters
import tricera._
import tricera.acsl.FunctionContract
import tricera.concurrency.CCReader
import tricera.concurrency.ccreader.{ArrayLocation, CCHeapArrayPointer}
import tricera.params.TriCeraParameters

import scala.util.control.NonFatal

/** Best-effort contract refinement. Weakens preconditions and preserves
    postconditions on the old inputs, re-verifies refined contracts 
    using the contracted function. */
object ACSLContractRefiner {
  def apply(result : Result, printed : ACSLResult, reader : CCReader,
            checker : ACSLContractVerifier) : ACSLResult = result match {
    case solution : Solution =>
      val frames = printed.contracts.map(c => c.funcName -> c.assigns).toMap
      val refined = new Refiner(reader, checker, frames).apply(solution)
      val output = ACSLLineariser(refined)
      output.copy(contracts = output.contracts.map(c =>
        c.copy(assigns = frames.getOrElse(c.funcName, None))))
    case _ => printed
  }

  private object BudgetExceeded extends RuntimeException

  private class Refiner(reader : CCReader, checker : ACSLContractVerifier,
                        frames : Map[String, Option[String]]) {
    private val settings = TriCeraParameters.get
    private var deadline = 0L
    private lazy val contexts = checker.contexts
    private var attempts = 0

    private val implications =
      scala.collection.mutable.Set[(Set[IFormula], Set[IFormula])]()

    private val parsedContracts = scala.collection.mutable.Map[
      (String, IFormula, IFormula), FunctionContract]()

    def apply(solution : Solution) : Solution = {
      val byId = solution.functionInvariants.map(i => i.id -> i).toMap
      val visited = scala.collection.mutable.Set[String]()
      val updated = scala.collection.mutable.Map[String, FunctionInvariants]()
      def update(id : String) : Unit = if (visited.add(id) && byId.contains(id)) {
        checker.callees(id).foreach(update)
        updated(id) = refine(byId(id))
      }
      byId.keys.toSeq.sorted.foreach(update)
      solution.copy(functionInvariants = solution.functionInvariants.map(i => updated(i.id)))
    }

    private trait RefinementStage {
      def apply(current : FunctionInvariants, checks : CandidateChecks) : FunctionInvariants
    }

    private val beforeSearch = Seq[RefinementStage](GeneraliseGlobals)
    private val searchStages = Seq[RefinementStage](
      WeakenPrecondition, GeneraliseBranches, WeakenBranches, StrengthenPostcondition)
    private val afterSearch = Seq[RefinementStage](AddValidity)

    private def refine(initial : FunctionInvariants) : FunctionInvariants = {
      if (initial.isSrcAnnotated || !reader.getFunctionContexts.contains(initial.id) ||
          reader.getContractVerificationClauses(initial.id).isEmpty)
        return initial

      // limit each function separately
      deadline = if (!settings.contractTimeouts) Long.MaxValue
                 else System.nanoTime() + settings.refineACSLTimeout.toLong * 1000000L
      attempts = 0
      var checks = Option.empty[CandidateChecks]
      try {
        if (!hasBudget) return initial
        val candidateChecks = new CandidateChecks(initial)
        checks = Some(candidateChecks)
        var current = beforeSearch.foldLeft(initial) { (inv, stage) =>
          stage(inv, candidateChecks)
        }
        var changed = true
        while (changed && hasBudget) {
          val next = searchStages.iterator.takeWhile(_ => hasBudget)
            .map(stage => stage(current, candidateChecks)).find(_ != current)
          changed = next.isDefined
          // restart after an improvement using the updated contract
          current = next.getOrElse(current)
        }
        afterSearch.foldLeft(current) { (inv, stage) =>
          stage(inv, candidateChecks)
        }
      } catch {
        case e @ (tricera.Main.StoppedException | tricera.Main.TimeoutException) => throw e
        case NonFatal(e) =>
          Util.printlnDebug("ACSL refinement skipped " + initial.id + ": " + e.toString)
          checks.map(_.lastAccepted).getOrElse(initial)
      } finally {
        Util.printlnDebug(s"ACSL refinement solver queries: $attempts (${initial.id})")
      }
    }

    private object GeneraliseGlobals extends RefinementStage {
      def apply(current : FunctionInvariants, checks : CandidateChecks) : FunctionInvariants = {
        val globals = LineariseVisitor(current.preCondition.invariant.expression,
                                       IBinJunctor.And).collect {
          case f @ EqLit(IConstant(v : ProgVarProxy), _) if v.isGlobal && !v.isPointer => f
        }
        // g == 3 before, g == 4 after --> g == old(g) + 1
        // Split a group when its combined generalization fails.
        def generalise(current : FunctionInvariants, group : Seq[IFormula])
        : FunctionInvariants = {
          if (group.isEmpty || !checks.hasBudget) return current
          val values = group.collect {
            case EqLit(IConstant(v : ProgVarProxy), n) => v.name -> (v, n)
          }.toMap
          val post = Rewriter.rewrite(current.postCondition.invariant.expression, {
            case EqLit(lhs @ IConstant(v : ProgVarProxy), n)
                if v.isGlobal && v.isPostExec && values.contains(v.name) =>
              val (before, value) = values(v.name)
              lhs === new Simplifier().apply(
                IConstant(before.copy(state = ProgVarProxy.State.PreExec)) + (n - value))
            case e => e
          }).asInstanceOf[IFormula]
          val pre = LineariseVisitor(current.preCondition.invariant.expression,
                                     IBinJunctor.And).filterNot(group.toSet)
          checks.accept(current, withPost(withPre(current, and(pre)), post)) match {
            case Some(refined) => refined
            case None if group.size > 1 =>
              val (left, right) = group.splitAt(group.size / 2)
              generalise(generalise(current, left), right)
            case None => current
          }
        }
        generalise(current, globals)
      }
    }

    private object WeakenPrecondition extends RefinementStage {
      def apply(current : FunctionInvariants, checks : CandidateChecks) : FunctionInvariants = {
        var result = current
        def accept(proposed : FunctionInvariants) : Boolean = {
          val accepted = checks.accept(current, proposed)
          accepted.foreach(result = _)
          accepted.isDefined
        }
        var changed = false
        val pre = LineariseVisitor(current.preCondition.invariant.expression,
                                   IBinJunctor.And)
        // try concrete equalities first
        val order = pre.indices.sortBy(i => pre(i) match {
          case EqLit(_, _) => 0
          case _ => 1
        })
        for (i <- order if !changed && checks.hasBudget) {
          val weakerPre = and(pre.patch(i, Nil, 1))
          if (accept(withPre(current, weakerPre)))
            changed = true
          else {
            val fixed = pre(i) match {
              case EqLit(IConstant(v : ProgVarProxy), _) if v.isPointer => None
              case EqLit(term, n) => Some((term, n))
              case _ => None
            }
            for ((term, n) <- fixed if !changed) {
              // generalize a concrete postcondition before relaxing the precondition
              val post = checks.withoutEntryFacts(current.postCondition.invariant.expression)
              val indices = term match {
                case IConstant(v : ProgVarProxy) if v.isParameter =>
                  Seq(generaliseIndices(post, v, IIntLit(n)))
                case _ => Nil
              }
              for (generalised <- (indices ++ generaliseValues(post, term, n)).distinct
                   if !changed && checks.hasBudget) {
                val candidate = withPost(withPre(current, weakerPre), generalised)
                if (accept(candidate) ||
                    accept(withPre(candidate, weakerPre &&& readBounds(candidate))))
                  changed = true
              }
              if (!changed && checks.hasBudget &&
                  (accept(withPre(current, weakerPre &&& (term >= n))) ||
                   accept(withPre(current, weakerPre &&& (term <= n)))))
                changed = true
            }
          }
        }
        result
      }

      // replace concrete indices, e.g. x[1] --> x[n]
      private def generaliseIndices(post : IFormula, variable : ProgVarProxy,
                                     value : IIntLit) : IFormula = {
        val visitor = new CollectingVisitor[Unit, IExpression] {
          override def postVisit(t : IExpression, arg : Unit,
                                 subres : Seq[IExpression]) : IExpression =
            (t update subres) match {
              case IFunApp(f, Seq(base, index : IIntLit)) if arrayReads(f) =>
                IFunApp(f, Seq(base, new Simplifier().apply(
                  index + IConstant(variable) - value)))
              case other => other
            }
        }
        visitor.visit(post, ()).asInstanceOf[IFormula]
      }

      // requires *p == 0, ensures *p == 2 can become ensures *p == old(*p) + 2.
      // For nonzero constants also try scaling, e.g., 21 -> 42 becomes 2 * old(x).
      private def generaliseValues(post : IFormula, term : ITerm,
                                    value : ap.basetypes.IdealInt) : Seq[IFormula] = {
        val oldFunctions = Map(ACSLExpression.deref -> ACSLExpression.oldDeref,
          ACSLExpression.arrow -> ACSLExpression.oldArrow,
          ACSLExpression.arrayAccess -> ACSLExpression.oldArrayAccess,
          ACSLExpression.arrayFieldAccess -> ACSLExpression.oldArrayFieldAccess)
        val before = Rewriter.rewrite(term, {
          case IFunApp(f, args) if oldFunctions.contains(f) => IFunApp(oldFunctions(f), args)
          case e => e
        }).asInstanceOf[ITerm]
        def rewrite(scale : Boolean, resultOnly : Boolean) : IFormula = {
          def selected(term : ITerm) = !resultOnly || (term match {
            case IConstant(v : ProgVarProxy) => v.isResult
            case _ => false
          })
          val visitor = new CollectingVisitor[Unit, IExpression] {
            override def postVisit(t : IExpression, arg : Unit,
                                   subres : Seq[IExpression]) : IExpression =
              (t update subres) match {
                case EqLit(lhs, n) if selected(lhs) && !scale => lhs === new Simplifier().apply(before + (n - value))
                case EqLit(lhs, n) if selected(lhs) && !value.isZero && (n % value).isZero =>
                  lhs === new Simplifier().apply(before * (n / value))
                case other => other
              }
          }
          visitor.visit(post, ()).asInstanceOf[IFormula]
        }
        (for (resultOnly <- Seq(true, false);
              scale <- if (value.isZero) Seq(false) else Seq(false, true))
          yield rewrite(scale, resultOnly)).distinct
      }
    }

    private object GeneraliseBranches extends RefinementStage {
      // (x == a && n == 1) || (x == b && n == 2) -->
      // (x == a && n < size(a)) || (x == b && n < size(b)).
      def apply(current : FunctionInvariants, checks : CandidateChecks) : FunctionInvariants = {
        val pre = LineariseVisitor(current.preCondition.invariant.expression, IBinJunctor.And)
        val candidates =
          for (i <- pre.indices.iterator;
               branches = LineariseVisitor(pre(i), IBinJunctor.Or) if branches.size > 1;
               outside = and(pre.patch(i, Nil, 1));
               generalised = branches.map { branch =>
                 val terms = LineariseVisitor(branch, IBinJunctor.And)
                 val kept = terms.filterNot {
                   case EqLit(IConstant(p : ProgVarProxy), _) => !p.isPointer
                   case _ => false
                 }
                 if (kept.size == terms.size) branch else {
                   val weaker = and(kept)
                   weaker &&& readBounds(withPre(current, outside &&& weaker))
                 }
               };
               if generalised != branches)
            yield withPre(current, outside &&& or(generalised))
        checks.firstAccepted(current, candidates)
      }
    }

    private object WeakenBranches extends RefinementStage {
      // try removing one conjunct from one branch
      def apply(current : FunctionInvariants, checks : CandidateChecks) : FunctionInvariants = {
        val pre = LineariseVisitor(current.preCondition.invariant.expression, IBinJunctor.And)
        val candidates =
          for (i <- pre.indices.iterator;
               branches = LineariseVisitor(pre(i), IBinJunctor.Or) if branches.size > 1;
               j <- branches.indices.iterator;
               terms = LineariseVisitor(branches(j), IBinJunctor.And);
               k <- terms.indices.iterator;
               if (terms(k) match {
                 case EqLit(IConstant(p : ProgVarProxy), _) => !p.isPointer
                 case _ : IIntFormula => true
                 case _ => false
               });
               branch = and(terms.patch(k, Nil, 1));
               outside = and(pre.patch(i, Nil, 1));
               // only add bounds for equalities to avoid reintroducing removed bounds
               withBounds = terms(k) match {
                 case EqLit(_, _) => Some(branch &&&
                   readBounds(withPre(current, outside &&& branch)))
                 case _ => None
               };
               replacement <- Iterator.single(branch) ++ withBounds.iterator)
            yield withPre(current, outside &&& or(branches.updated(j, replacement)))
        checks.firstAccepted(current, candidates)
      }
    }

    private object StrengthenPostcondition extends RefinementStage {
      def apply(current : FunctionInvariants, checks : CandidateChecks) : FunctionInvariants = {
        // try to strengthen disequalities, e.g. x != 10 || r != 0 becomes x <= 0 || r != 0.
        def strongerGuards(f : IFormula) : Seq[IFormula] = f match {
          case INot(EqLit(term, n)) =>
            Seq(term <= 0, term >= 0, term < n, term > n).distinct
          case _ => Nil
        }

        val post = LineariseVisitor(current.postCondition.invariant.expression, IBinJunctor.And)
        val candidates =
          for (i <- post.indices.iterator;
               parts = LineariseVisitor(post(i), IBinJunctor.Or) if parts.size > 1;
               j <- parts.indices.iterator;
               replacement <- (Seq(or(parts.patch(j, Nil, 1))) ++
                 strongerGuards(parts(j)).map(f => or(parts.updated(j, f)))).iterator)
            yield withPost(current, and(post.updated(i, replacement)))
        checks.firstAccepted(current, candidates)
      }
    }

    private object AddValidity extends RefinementStage {
      def apply(current : FunctionInvariants, checks : CandidateChecks) : FunctionInvariants =
        missingValidity(current).takeWhile(_ => checks.hasBudget).foldLeft(current) {
          (inv, valid) =>
            checks.accept(inv, withPost(inv, inv.postCondition.invariant.expression &&& valid))
              .getOrElse(inv)
        }

      private def missingValidity(inv : FunctionInvariants) : Iterator[IFormula] = {
        val post = inv.postCondition.invariant.expression
        def address(p : ProgVarProxy) = IConstant(p.copy(state =
          if (p.isParameter) ProgVarProxy.State.PreExec else ProgVarProxy.State.PostExec))
        val existing = LineariseVisitor(post, IBinJunctor.And).collect {
          case IAtom(ACSLExpression.valid, Seq(IConstant(p : ProgVarProxy))) =>
            if (p.isParameter) address(p) else IConstant(p)
        }
        val values = ValSetReader(post)
        val pointers = SymbolCollector.constants(inv.preCondition.invariant.expression & post)
          .collect { case p : ProgVarProxy if p.isPointer && (p.isParameter || p.isGlobal) => p }
          .toSeq.groupBy(p => (p.name, p.scope)).toSeq.sortBy {
            case ((name, scope), _) =>
              (if (scope == ProgVarProxy.Scope.Parameter) 0 else 1, name)
          }
        pointers.iterator.map { case (_, aliases) => address(aliases.head) }
          .filterNot(p => existing.exists(values.areEqual(_, p)))
          .distinctBy(p => values.getVal(p).getOrElse(Val(Set(p))))
          .map(p => IAtom(ACSLExpression.valid, Seq(p)))
      }
    }

    private class CandidateChecks(initial : FunctionInvariants) {
      private val initialContract = parse(initial)
      private val facts = contexts(initial.id).globalArrayPrecondition
      private def conjuncts(f : IFormula) = LineariseVisitor(f, IBinJunctor.And)
      private val empty = withPost(withPre(initial, IBoolLit(true)), IBoolLit(true))
      private def parsePre(f : IFormula) = parse(withPre(empty, f)).pre
      private val entryFacts = findEntryFacts(initial, initialContract, facts)
      def withoutEntryFacts(f : IFormula) = and(conjuncts(f).filterNot(entryFacts))
      private val seen = scala.collection.mutable.Set(
        (conjunctSet(initialContract.pre), conjunctSet(initialContract.post)))
      private val rejected = scala.collection.mutable.ArrayBuffer[
        (Set[IFormula], Set[IFormula])]()
      private val prePredicates = reader.getFunctionContexts.values.map(_.prePred.pred).toSet
      private val hasContractCalls = reader.getContractVerificationClauses(initial.id).get
        .exists(c => prePredicates(c.head.pred))

      // keep checked changes if a later stage fails
      private var accepted = initial
      def lastAccepted : FunctionInvariants = accepted

      def hasBudget : Boolean = Refiner.this.hasBudget

      def firstAccepted(current : FunctionInvariants, candidates : Iterator[FunctionInvariants])
      : FunctionInvariants =
        candidates.takeWhile(_ => hasBudget).map(accept(current, _))
          .collectFirst { case Some(refined) => refined }.getOrElse(current)

      def accept(current : FunctionInvariants, proposed : FunctionInvariants)
      : Option[FunctionInvariants] = try {
        if (!hasBudget) return None
        val candidate = withPost(proposed,
          withoutEntryFacts(proposed.postCondition.invariant.expression))
        val previous = parse(current)
        val parsed = parse(candidate)
        val key = (conjunctSet(parsed.pre), conjunctSet(parsed.post))
        if (!seen.add(key)) return None
        // prune related candidates only when no callee summaries are involved
        if (!hasContractCalls && rejected.exists { case (pre, post) =>
              key._1.subsetOf(pre) && post.subsetOf(key._2)
            }) return None
        // keep validity requirements, including locations the body never reads
        val validity = conjuncts(current.preCondition.invariant.expression)
          .filter(f => ContainsSymbol(f, (e : IExpression) => e match {
            case IAtom(ACSLExpression.valid, _) => true
            case _ => false
          }))
        val validityOk = validity.isEmpty ||
          validity.forall(conjuncts(candidate.preCondition.invariant.expression).contains) ||
          implies(facts &&& parsed.pre, parsePre(and(validity)))
        // Preserve the postcondition on the previous contract's inputs.
        val preOk = validityOk && implies(facts &&& previous.pre, parsed.pre)
        val postOk = preOk &&
          implies(facts &&& previous.pre &&& parsed.post, previous.post)
        val verdict = if (postOk) verify(candidate) else None
        if (!hasContractCalls && verdict.contains(false)) rejected += key
        val verified = verdict.contains(true)
        if (settings.printDebugMessages)
          Util.printlnDebug(s"ACSL refinement candidate: pre=$preOk post=$postOk body=$verified " +
            printed(candidate))
        if (verified) {
          // old loop invariants may not hold for the new inputs
          val refined = if (parsed.pre == previous.pre) candidate
                        else candidate.copy(loopInvariants = Nil)
          accepted = refined
          Some(refined)
        } else None
      } catch {
        case e @ (tricera.Main.StoppedException | tricera.Main.TimeoutException) => throw e
        case NonFatal(e) =>
          Util.printlnDebug("ACSL refinement skipped candidate: " + e.toString)
          None
      }
    }

    private def findEntryFacts(initial : FunctionInvariants, contract : FunctionContract,
                               facts : IFormula) : Set[IFormula] = {
      val empty = withPost(withPre(initial, IBoolLit(true)), IBoolLit(true))
      def parsePost(f : IFormula) = parse(withPost(empty, f)).post
      val entry = facts &&& contract.pre
      val inputs = SymbolCollector.constants(entry)
      // a map from post exprs to pre exprs that are equal
      val entryValues = ValSetReader(contract.post).vals.flatMap { value =>
        val (old, other) = value.variants.partition { t =>
          val constants = SymbolCollector.constants(t)
          constants.nonEmpty && constants.subsetOf(inputs) &&
            SymbolCollector.variables(t).isEmpty
        }
        old.toSeq.sortBy(_.toString).headOption.toSeq.flatMap { before =>
          other.filter(t => SymbolCollector.constants(t).nonEmpty).map(_ -> before)
        }
      }.toMap
      // e.g. requires x > 0 implies ensures old(x) >= 0
      LineariseVisitor(initial.postCondition.invariant.expression, IBinJunctor.And).iterator
        .takeWhile(_ => hasBudget).filter { f =>
          val parsed = parsePost(f)
          // keep eqs that relate current vals to those at entry
          val atEntry = parsed match {
            case IIntFormula(IIntRelation.GeqZero, _) =>
              Rewriter.rewrite(parsed, {
                case t: ITerm => entryValues.getOrElse(t, t)
                case e => e
              }).asInstanceOf[IFormula]
            case _ => parsed
          }
          SymbolCollector.constants(atEntry).subsetOf(inputs) && implies(entry, atEntry)
        }.toSet
    }

    private val arrayReads = Set(ACSLExpression.arrayAccess,
      ACSLExpression.oldArrayAccess, ACSLExpression.arrayAccessOldPointer)

    private def readBounds(inv : FunctionInvariants) : IFormula = {
      val sizes = contexts(inv.id).prePred.argVars.flatMap(v => v.typ match {
        case p : CCHeapArrayPointer if p.arrayLocation == ArrayLocation.Global =>
          p.declaredSize.map(v.name.stripSuffix(Literals.preExecSuffix) -> _)
        case _ => None
      }).toMap
      val aliases = ValSetReader(inv.preCondition.invariant.expression)
      def bounds(base : ITerm, index : ITerm) : Option[IFormula] = base match {
        case IConstant(p : ProgVarProxy) if p.isGlobal && sizes.contains(p.name) =>
          Some((index >= 0) &&& (index < sizes(p.name)))
        case IFunApp(f, Seq(base, offset)) if f == ACSLExpression.pointerOffset =>
          bounds(base, new Simplifier().apply(index + offset))
        case _ => None
      }
      val conditions = scala.collection.mutable.LinkedHashSet[IFormula]()
      val visitor = new CollectingVisitor[Unit, Unit] {
        override def postVisit(t : IExpression, arg : Unit,
                               subres : Seq[Unit]) : Unit = t match {
          case IFunApp(f, Seq(base, index)) if arrayReads(f) =>
            val variants = Seq(base) ++ aliases.getVal(base).toSeq.flatMap(_.variants)
            variants.iterator.flatMap(bounds(_, index)).take(1).foreach(conditions += _)
          case _ =>
        }
      }
      visitor.visit(inv.postCondition.invariant.expression, ())
      and(conditions)
    }

    private def parse(inv : FunctionInvariants) : FunctionContract =
      parsedContracts.getOrElseUpdate((inv.id, inv.preCondition.invariant.expression,
        inv.postCondition.invariant.expression), checker.parse(printed(inv)))

    private def printed(inv : FunctionInvariants) : ACSLLinearisedContract =
      ACSLLineariser(Solution(Seq(inv), Nil)).contracts.head.copy(
        assigns = frames.getOrElse(inv.id, None))

    private def verify(inv : FunctionInvariants) : Option[Boolean] = {
      if (!hasBudget) return None
      attempts += 1
      checker.check(printed(inv), math.max(1L, math.min(1000L, remaining)))
    }

    private def implies(assumptions : IFormula, conclusion : IFormula) : Boolean = {
      val from = conjunctSet(assumptions)
      val to = conjunctSet(conclusion)
      val key = (from, to)
      if (to.subsetOf(from) || from(IBoolLit(false)) || implications(key))
        return true
      val proved = attempt {
        SimpleAPI.withProver { p =>
          val formula = assumptions &&& !conclusion
          p.addConstants(SymbolCollector.constantsSorted(formula))
          val theories = new TheoryCollector
          theories(formula)
          p.addTheories(theories.theories)
          p.addAssertion(formula)
          if (!settings.contractTimeouts)
            ACSLContractVerifier.checkSat(p) == SimpleAPI.ProverStatus.Unsat
          else p.withTimeout(math.max(1L, math.min(200L, remaining))) {
            p.??? == SimpleAPI.ProverStatus.Unsat
          }
        }
      }.contains(true)
      if (proved) implications += key
      proved
    }

    private def remaining : Long = (deadline - System.nanoTime()) / 1000000L

    private def hasBudget : Boolean = {
      GlobalParameters.get.timeoutChecker()
      attempts < settings.refineACSLAttempts && remaining > 0
    }

    private def attempt[A](check : => A) : Option[A] = {
      if (!hasBudget) return None
      attempts += 1
      val params = GlobalParameters.get.clone
      val outerCheck = params.timeoutChecker
      val queryDeadline = math.min(deadline, System.nanoTime() + 1000000000L)
      params.timeoutChecker = () => {
        outerCheck()
        if (settings.contractTimeouts && System.nanoTime() >= queryDeadline) throw BudgetExceeded
      }
      try {
        val result = GlobalParameters.withValue(params) {
          ACSLContractVerifier.withQueryBudget { check }
        }
        outerCheck()
        Some(result)
      } catch {
        case e @ (tricera.Main.StoppedException | tricera.Main.TimeoutException) => throw e
        case NonFatal(e) =>
          Util.printlnDebug("ACSL refinement skipped query: " + e.toString)
          None
      }
    }

    private def conjunctSet(f : IFormula) : Set[IFormula] =
      LineariseVisitor(new Simplifier().apply(f), IBinJunctor.And)
        .filterNot(_ == IBoolLit(true)).toSet

    private def withPre(inv : FunctionInvariants, f : IFormula) =
      inv.copy(preCondition = PreCondition(inv.preCondition.invariant.copy(expression = f)))

    private def withPost(inv : FunctionInvariants, f : IFormula) =
      inv.copy(postCondition = PostCondition(inv.postCondition.invariant.copy(expression = f)))
  }
}
