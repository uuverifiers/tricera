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
import tricera._
import tricera.acsl.ACSLTranslator
import tricera.concurrency.CCReader
import tricera.concurrency.CallSiteTransform.CallSiteTransforms
import tricera.concurrency.ccreader.{CCHeapArrayPointer, CCHeapPointer, CCVar}

import scala.util.control.NonFatal

/** Tries to add assigns clauses from the solution if they can be verified. */
object ACSLFrameInference {
  def apply(printed : ACSLResult, inferred : Result, reader : CCReader,
            transforms : CallSiteTransforms, checker : ACSLContractVerifier) : ACSLResult =
    inferred match {
      case source : Solution =>
        val contexts = reader.getFunctionContexts
        val sources = source.functionInvariants.map(i => i.id -> i).toMap
        val additions = transforms.map(_.getAstAdditions())
        val introducedGlobals = additions.iterator.flatMap(_.introducedGlobalVariables.keys).toSet
        // transformed functions omit parameters whose cells became globals
        val stackParams = (for (a <- additions;
                                (transformed, original) <- a.transformedFunctionIdToOriginalId;
                                from <- contexts.get(original);
                                to <- contexts.get(transformed)) yield {
          val removed = from.acslContext.getParams.map(_.name).toSet --
                        to.acslContext.getParams.map(_.name)
          original -> removed
        }).groupMapReduce(_._1)(_._2)(_ ++ _)

        def addFrame(contract : ACSLLinearisedContract) : ACSLLinearisedContract = {
          val id = contract.funcName
          try {
            val candidate = for (inv <- sources.get(id) if !inv.isSrcAnnotated;
                                 context <- contexts.get(id);
                                 locations <- extractLocations(inv, context.acslContext,
                                   introducedGlobals, stackParams.getOrElse(id, Set.empty))) yield
              contract.copy(assigns = Some(ACSLLineariser.assignsString(
                locations, inv.preCondition)))
            // e.g., an inferred heap update at p gives assigns *p
            candidate.filter(c => checker.verify(c)).getOrElse(contract)
          } catch {
            case e @ (tricera.Main.StoppedException | tricera.Main.TimeoutException) => throw e
            case NonFatal(e) =>
              Util.printlnDebug("ACSL frame skipped " + id + ": " + e.toString)
              contract
          }
        }

        val byId = printed.contracts.map(c => c.funcName -> c).toMap
        val visited = scala.collection.mutable.Set[String]()
        val updated = scala.collection.mutable.Map[String, ACSLLinearisedContract]()
        def update(id : String) : Unit = if (visited.add(id) && byId.contains(id)) {
          checker.callees(id).foreach(update)
          updated(id) = addFrame(byId(id))
        }
        byId.keys.toSeq.sorted.foreach(update)
        printed.copy(contracts = printed.contracts.map(c => updated(c.funcName)))
      case _ => printed
    }

  /** Find possible assigns locations from the solution. */
  private def extractLocations(inv : FunctionInvariants, context : ACSLTranslator.FunctionContext,
                               introducedGlobals : Set[String], stackParams : Set[String])
  : Option[Seq[ITerm]] = {
    val globals = context.getGlobals.filterNot(v => introducedGlobals(v.name))
    val parameters = context.getParams.map(_.name).toSet
    if (globals.exists(v => parameters(v.name)) ||
        globals.map(_.name).distinct.size != globals.size)
      return None

    val pre = inv.preCondition.invariant.expression
    val post = inv.postCondition.invariant.expression
    val constants = SymbolCollector.constants(pre &&& post).collect {
      case p : ProgVarProxy => p
    }
    val values = ValSetReader(pre &&& post)

    val stackLocations = extractStackLocations(context.getParams, stackParams, values)
    val globalLocations = extractGlobalLocations(globals, constants, values)
    val heapLocations = extractHeapLocations(inv, context, constants, values)
    heapLocations.map(cells => (globalLocations ++ stackLocations ++ cells).distinct)
  }

  // stack-pointer arguments encoded as globals
  private def extractStackLocations(params : Seq[CCVar], stackParams : Set[String],
                                    values : ValSet) : Seq[ITerm] =
    params.filter(p => stackParams(p.name)).flatMap { p =>
      val before = ProgVarProxy(p.name, ProgVarProxy.State.PreExec,
        ProgVarProxy.Scope.Parameter, true)
      val after = before.copy(state = ProgVarProxy.State.PostExec)
      val oldValue = ACSLExpression.derefFunApp(ACSLExpression.oldDeref, before)
      val newValue = ACSLExpression.derefFunApp(ACSLExpression.deref, after)
      if (values.areEqual(oldValue, newValue)) None
      else Some(ACSLExpression.derefFunApp(ACSLExpression.deref, before))
    }

  // globals omitted from assigns must stay unchanged
  private def extractGlobalLocations(globals : Seq[CCVar],
                                     constants : scala.collection.Set[ProgVarProxy],
                                     values : ValSet) : Seq[ITerm] =
    globals.filterNot { v =>
      val old = constants.find(p => p.name == v.name && p.isGlobal && p.isPreExec)
      val current = constants.find(p => p.name == v.name && p.isGlobal && p.isPostExec)
      (for (a <- old; b <- current) yield values.areEqual(IConstant(a), IConstant(b)))
        .getOrElse(false)
    }.map { v =>
      IConstant(ProgVarProxy(v.name, ProgVarProxy.State.PreExec,
        ProgVarProxy.Scope.Global, v.typ.isInstanceOf[CCHeapPointer] ||
                                  v.typ.isInstanceOf[CCHeapArrayPointer])) : ITerm
    }

  private def extractHeapLocations(inv : FunctionInvariants,
                                   context : ACSLTranslator.FunctionContext,
                                   constants : scala.collection.Set[ProgVarProxy],
                                   values : ValSet) : Option[Seq[ITerm]] =
    inv.postCondition.invariant.heapInfo match {
      case None => if (context.isHeapEnabled) None else Some(Seq.empty[ITerm])
      case Some(info) =>
        val before = constants.find(p => info.isHeap(p) && p.isPreExec)
        val after = constants.find(p => info.isHeap(p) && p.isPostExec)
        val visitor = new ACSLExpressionProcessor.ACSLExpressionVisitor(
          info, inv.preCondition,
          inv.preCondition.invariant.expression &&& inv.postCondition.invariant.expression)

        // assigns must be expressible using values at function entry
        def entryTerm(t : ITerm) : Boolean =
          SymbolCollector.variables(t).isEmpty && SymbolCollector.constants(t).forall {
            case p : ProgVarProxy => p.isPreExec && (p.isParameter || p.isGlobal)
            case _ => false
          }

        // prefer parameters over other vars
        def entryNames(t : ITerm) : ITerm = Rewriter.rewrite(t, {
          case term : ITerm =>
            values.getVal(term).toSeq.flatMap(_.variants).collect {
              case c @ IConstant(p : ProgVarProxy) if p.isPreExec && !info.isHeap(p) => (c, p)
            }.sortBy { case (_, p) => (if (p.isParameter) 0 else 1, p.name) }
              .headOption.map(_._1).getOrElse(term)
          case e => e
        }).asInstanceOf[ITerm]

        // use the written value's type to translate a read at this address to *p, a[i], etc.
        def location(address : ITerm, value : ITerm, oldHeap : ITerm) : Option[ITerm] =
          value match {
            case IFunApp(ctor, _) => info.objectCtorToSelector(ctor).flatMap { selector =>
              val read = IFunApp(selector, Seq(info.heap.read(oldHeap, entryNames(address))))
              val translated = visitor.visit(read, ()).asInstanceOf[ITerm]
              if (entryTerm(translated) && !ContainsTOHVisitor(translated, info))
                Some(translated)
              else None
            }
            case _ => None
          }

        // h_post = write(write(h_pre, p, v), q, w) --> assigns *p, *q
        def writes(t : ITerm, oldHeap : ITerm) : Option[Seq[ITerm]] =
          if (values.areEqual(t, oldHeap)) Some(Nil) else t match {
            case IFunApp(write, Seq(base, address, value)) if info.isWriteFun(write) =>
              for (rest <- writes(base, oldHeap);
                   cell <- location(address, value, oldHeap)) yield rest :+ cell
            case _ => None
          }

        for (old <- before; current <- after;
             heapLocations <- values.getVal(IConstant(current)).toSeq
               .flatMap(_.variants).sortBy(_.toString).iterator
               .map(t => writes(t, IConstant(old))).collectFirst { case Some(cells) => cells }) yield heapLocations
    }
}
