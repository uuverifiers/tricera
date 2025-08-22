/**
 * Copyright (c) 2025 Scania CV AB. All rights reserved.
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

import ap.parser.{IConstant, IFormula, VariableSubstVisitor}
import lazabs.horn.preprocessor.HornPreprocessor


import tricera.{
    CounterExample, Empty,
    FunctionInvariants, HeapInfo, Invariant, Literals, LoopInvariant, 
    PostCondition, PreCondition, ProgVarProxy, Result, Solution}
import tricera.concurrency.CCReader
import tricera.concurrency.ccreader.{
    CCVar, CCHeapPointer, CCHeapArrayPointer, CCStackPointer}
import tricera.Util.SourceInfo
import tricera.Util.printlnDebug


object ResultConverter {
  def hornSolverSolutionToResult
    (reader: CCReader, entryFunction: String)
    (result: Either[Option[HornPreprocessor.Solution], hornconcurrency.VerificationLoop.Counterexample])
    : Result = {
    import scala.collection.mutable.HashSet
    import Literals.{invPrefix, postExecSuffix, preExecSuffix, resultExecSuffix}

    def replacePredVarWithFunctionParam(formula: IFormula, predVars: Seq[CCVar], funcParams: Seq[String]): IFormula = {
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
      inv: (CCReader.CCPredicate, SourceInfo),
      solution: SolutionProcessor.Solution,
      heapInfo: Option[HeapInfo],
      paramNames: Seq[String])
      : LoopInvariant = {
        val (ccPred, srcInfo) = inv
        val (_, form) = solution.find(
          p => p._1.name.stripPrefix(invPrefix) == ccPred.pred.name).get
        LoopInvariant(replacePredVarWithFunctionParam(form, ccPred.argVars, paramNames), heapInfo, srcInfo)
    }

    def toFunctionInvariants(
      funcId: String,
      heapInfo: Option[HeapInfo],
      ctx: CCReader.FunctionContext,
      solution: SolutionProcessor.Solution,
      loopInvs: Map[String,(CCReader.CCPredicate, SourceInfo)],
      annotatedFuncs: HashSet[String])
      = {
      val paramNames = ctx.acslContext.getParams.map(v => v.name)
      FunctionInvariants(
        funcId,
        annotatedFuncs(funcId),
        PreCondition(Invariant(
          replacePredVarWithFunctionParam(
            solution(ctx.prePred.pred),
            ctx.prePred.argVars,
            paramNames),
          heapInfo,
          ctx.prePred.srcInfo)),
        PostCondition(Invariant(
          replacePredVarWithFunctionParam(
            solution(ctx.postPred.pred),
            ctx.postPred.argVars,
            paramNames),
          heapInfo,
          ctx.postPred.srcInfo)),
        loopInvs
          .withFilter(i => i._1.startsWith(funcId))
          .map(i => toLoopInvariant(i._2, solution, heapInfo, paramNames)).toList)
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
}
