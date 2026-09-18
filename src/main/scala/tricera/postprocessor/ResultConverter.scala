/**
 * Copyright (c) 2025 Scania CV AB
 *               2026 Zafer Esen. All rights reserved.
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

import ap.parser.{CollectingVisitor, ConstantSubstVisitor, IConstant, IExpression, IFormula,
                  IFunApp, IIntLit, ISortedVariable, ITerm, Simplifier, SymbolCollector,
                  VariableSubstVisitor, IBoolLit, IQuantified, LineariseVisitor,
                  IBinJunctor}
import lazabs.horn.preprocessor.HornPreprocessor
import tricera._
import tricera.concurrency.CCReader
import tricera.concurrency.ccreader._
import tricera.Util.SourceInfo


object ResultConverter {
  def hornSolverSolutionToResult
    (reader: CCReader, system: hornconcurrency.ParametricEncoder.System)
    (result: Either[Option[HornPreprocessor.Solution], hornconcurrency.VerificationLoop.Counterexample])
    : Result = {
    import scala.collection.mutable.HashSet
    import Literals.{invPrefix, postExecSuffix, preExecSuffix, resultExecSuffix}

    def stripSuffix(name: String) = {
      if (name.endsWith(preExecSuffix)) {
        name.dropRight(preExecSuffix.size)
      } else if (name.endsWith(postExecSuffix)) {
        name.dropRight(postExecSuffix.size)
      } else if (name.endsWith(resultExecSuffix)) {
        name.dropRight(resultExecSuffix.size)
      } else {
        name
      }
    }

    def globalArraySizes(predVars: Seq[CCVar]): Map[String, Int] =
      (for (v <- predVars;
            size <- v.typ match {
              case p: CCHeapArrayPointer
                if p.arrayLocation == ArrayLocation.Global => p.declaredSize
              case _ => None
            })
       yield stripSuffix(v.name) -> size).toMap

    // a declared global array pointer has 0 offset and known size
    def resolveGlobalArrayFacts(formula: IFormula, predVars: Seq[CCVar],
                                heapInfo: Option[HeapInfo]): IFormula =
      heapInfo match {
        case Some(info) =>
          val sizes = globalArraySizes(predVars)
          if (sizes.isEmpty) formula
          else (new Simplifier)(
            GlobalArrayFactsVisitor(formula, sizes, info))
        case None => formula
      }

    def replacePredVarWithFunctionParam(formula: IFormula, predVars: Seq[CCVar], funcParams: Seq[String]): IFormula = {
      def nameToState(name: String):ProgVarProxy.State = {
        if (name.endsWith(preExecSuffix)) {
          ProgVarProxy.State.PreExec
        } else if (name.endsWith(postExecSuffix)) {
          ProgVarProxy.State.PostExec
        } else if (name.endsWith(resultExecSuffix)) {
          ProgVarProxy.State.Result
        } else {
          ProgVarProxy.State.Current
        }
      }

      def getScope(name: String): ProgVarProxy.Scope = {
        if (funcParams.contains(stripSuffix(name))) {
          ProgVarProxy.Scope.Parameter
        } else if (name.endsWith(resultExecSuffix)) {
          ProgVarProxy.Scope.Temporary
        } else {
          val globalVars = predVars
            .withFilter(
              v => v.name.endsWith(preExecSuffix) && 
              funcParams.find(p => stripSuffix(v.name) == p).isEmpty)
            .map(v => stripSuffix(v.name))
          if (globalVars.contains(stripSuffix(name))) {
            ProgVarProxy.Scope.Global
          } else {
            ProgVarProxy.Scope.Local
          }
        }
      }

      def isPointer(name: CCVar): Boolean = {
        name.typ match {
          case _: CCHeapPointer => true
          case _: CCStackPointer => true
          case _: CCHeapArrayPointer => true
          case _ => false
        }
      }

      VariableSubstVisitor.visit(
        formula, (predVars.map(
          p => IConstant(
            ProgVarProxy(
              stripSuffix(p.name),
              nameToState(p.name),
              getScope(p.name),
              isPointer(p)))).toList, 0))
      .asInstanceOf[IFormula]
    }

    def toLoopInvariant(
      inv: (CCPredicate, SourceInfo),
      solution: SolutionProcessor.Solution,
      heapInfo: Option[HeapInfo],
      paramNames: Seq[String])
      : LoopInvariant = {
        val (ccPred, srcInfo) = inv
        val (_, form) = solution.find(
          p => p._1.name.stripPrefix(invPrefix) == ccPred.pred.name).get
        LoopInvariant(
          resolveGlobalArrayFacts(
            replacePredVarWithFunctionParam(form, ccPred.argVars, paramNames),
            ccPred.argVars, heapInfo),
          heapInfo, srcInfo)
    }

    def toFunctionInvariants(
      funcId: String,
      heapInfo: Option[HeapInfo],
      ctx: CCReader.FunctionContext,
      solution: SolutionProcessor.Solution,
      loopInvs: Map[String,(CCPredicate, SourceInfo)],
      annotatedFuncs: HashSet[String])
      = {
      val paramNames = ctx.acslContext.getParams.map(v => v.name)
      val globalFacts = replacePredVarWithFunctionParam(
        ConstantSubstVisitor(ctx.globalArrayPrecondition,
          ctx.prePred.argVars.zipWithIndex.map { case (v, i) =>
            v.term -> ISortedVariable(i, v.sort)
          }.toMap), ctx.prePred.argVars, paramNames)
      FunctionInvariants(
        funcId,
        annotatedFuncs(funcId),
        PreCondition(Invariant(
          resolveGlobalArrayFacts(
            replacePredVarWithFunctionParam(
              solution(ctx.prePred.pred) &&& callSitePrecondition(ctx.prePred, solution),
              ctx.prePred.argVars,
              paramNames),
            ctx.prePred.argVars,
            heapInfo) &&& globalFacts,
          heapInfo,
          ctx.prePred.srcInfo)),
        PostCondition(Invariant(
          resolveGlobalArrayFacts(
            replacePredVarWithFunctionParam(
              solution(ctx.postPred.pred),
              ctx.postPred.argVars,
              paramNames),
            ctx.postPred.argVars,
            heapInfo),
          heapInfo,
          ctx.postPred.srcInfo)),
        loopInvs
          .withFilter(i => i._1.startsWith(funcId))
          .map(i => toLoopInvariant(i._2, solution, heapInfo, paramNames)).toList)
    }

    // recover caller facts that the inferred precondition may omit
    // e.g., increment(a, 1) and increment(b, 2) yield
    // (x == a && n == 1) || (x == b && n == 2)
    def callSitePrecondition(pre: CCPredicate,
                             solution: SolutionProcessor.Solution): IFormula = {
      import IExpression._
      val pointers = pre.argVars.filter(_.typ.isInstanceOf[CCHeapArrayPointer])
      if (pointers.isEmpty) return IBoolLit(true)
      val clauses = (system.assertions ++ system.backgroundAxioms.clauses ++
        system.processes.flatMap(_._1.map(_._1))).filter(_.head.pred == pre.pred)
      val byName = solution.map { case (p, f) => (p.name, p.arity) -> f }
      def bodySolution(p: Predicate): Option[IFormula] =
        solution.get(p).orElse(byName.get((invPrefix + p.name, p.arity)))
      if (clauses.isEmpty || clauses.exists(_.body.exists(a =>
            bodySolution(a.pred).isEmpty))) return IBoolLit(true)

      val args = pre.argVars.map(v => IConstant(v.term))

      def pointerAliases(form: IFormula): IFormula = {
        val values = ValSetReader(form)
        def knownOffset(term: ITerm): ITerm =
          values.getVal(term).toSeq.flatMap(_.variants)
            .find(t => !reader.getHeapInfo.exists(ContainsTOHVisitor(t, _)))
            .getOrElse(term)
        def components(v: CCVar): Seq[(ITerm, ITerm)] = {
          val ops = v.typ.asInstanceOf[CCHeapArrayPointer].ptrOps
          val term = IConstant(v.term)
          Seq((ops.getRange(term), ops.getOffset(term))) ++
            values.getVal(term).toSeq.flatMap(_.variants.collect {
              case IFunApp(c, Seq(range, offset)) if c == ops.ctor => (range, offset)
            })
        }
        val aliases = pointers.combinations(2).flatMap { case Seq(a, b) =>
          val left = IConstant(a.term)
          val right = IConstant(b.term)
          if (values.areEqual(left, right)) Seq(left === right)
          else for {
            (ra, oa) <- components(a)
            (rb, ob) <- components(b)
            if a.typ.asInstanceOf[CCHeapArrayPointer].elementType ==
               b.typ.asInstanceOf[CCHeapArrayPointer].elementType
            if values.areEqual(ra, rb)
            offset = new Simplifier().apply(knownOffset(ob) - knownOffset(oa))
            if SymbolCollector.variables(offset).isEmpty &&
               SymbolCollector.constants(offset).forall(pre.argVars.map(_.term).contains) &&
               !reader.getHeapInfo.exists(ContainsTOHVisitor(offset, _))
          } yield if (offset == IIntLit(0)) right === left
                  else right === IFunApp(ACSLExpression.pointerOffset, Seq(left, offset))
        }.toSeq
        val nested = form match {
          case Conj(_, _) =>
            and(LineariseVisitor(form, IBinJunctor.And).map(pointerAliases))
          case Disj(a, b) => pointerAliases(a) | pointerAliases(b)
          case IQuantified(Quantifier.EX, body) => pointerAliases(body)
          case _ => IBoolLit(true)
        }
        and(aliases) &&& nested
      }

      val incoming = or(for (clause <- clauses) yield {
        val (body, constraint) = clause.inline(args)
        val form = constraint & and(body.map { atom =>
          VariableSubstVisitor(bodySolution(atom.pred).get, (atom.args.toList, 0))
        })
        val projected = quanConsts(Quantifier.EX, SymbolCollector.constantsSorted(form)
          .filterNot(pre.argVars.map(_.term).contains), form)
        projected &&& pointerAliases(form)
      })
      ConstantSubstVisitor(incoming,
        pre.argVars.zipWithIndex.map { case (v, i) =>
          v.term -> ISortedVariable(i, v.sort)
        }.toMap)
    }

    result match {
      case Left(Some(solution)) =>
        val heapInfo = reader.getHeapInfo
        val loopInvs = reader.getLoopInvariants
        val annotatedFuncs = reader.funsWithAnnot

        val funcInvs = reader.getFunctionContexts
          .withFilter(
            // The solution to the horn system does not contain _pre/_post predicates
            // for the entry function. However the entry function may have a function
            // context if it is annotated with a contract or marked for contract inference.
            {case (funcId, ctx) => 
              (solution.get(ctx.prePred.pred).isDefined && solution.get(ctx.postPred.pred).isDefined)})
          .map(
            {case (funcId, ctx) =>
              toFunctionInvariants(funcId, heapInfo, ctx, solution, loopInvs, annotatedFuncs)})
          .toSeq

        val disassociatedLoopInvs = loopInvs
          .withFilter(lInv => !funcInvs.exists(fInv => lInv._1.startsWith(fInv.id)))
          .map(i => toLoopInvariant(i._2, solution, heapInfo, Seq())).toSeq

        Solution(funcInvs, disassociatedLoopInvs)
      case Left(None) => Empty()
      case Right(cex) => CounterExample(cex)
    }
  }

  private object GlobalArrayFactsVisitor {
    def apply(formula: IFormula, sizes: Map[String, Int],
              heapInfo: HeapInfo): IFormula =
      new GlobalArrayFactsVisitor(sizes, heapInfo)
        .visit(formula, ()).asInstanceOf[IFormula]
  }

  private class GlobalArrayFactsVisitor(
    sizes: Map[String, Int],
    heapInfo: HeapInfo
  ) extends CollectingVisitor[Unit, IExpression] {

    private def knownSize(t: ITerm): Option[Int] = t match {
      case IConstant(p: ProgVarProxy) if p.isGlobal => sizes.get(p.name)
      case _ => None
    }

    override def postVisit(
        t: IExpression,
        arg: Unit,
        subres: Seq[IExpression]
    ): IExpression = (t update subres) match {
      case IFunApp(offsetSel, Seq(arr))
          if heapInfo.isArrayPtrOffset(offsetSel) &&
            knownSize(arr).isDefined =>
        IIntLit(0)
      case IFunApp(rangeSize, Seq(IFunApp(rangeSel, Seq(arr))))
          if heapInfo.isRangeSize(rangeSize) &&
            heapInfo.isArrayPtrRange(rangeSel) &&
            knownSize(arr).isDefined =>
        IIntLit(knownSize(arr).get)
      case updated => updated
    }
  }
}
