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

import scala.collection.mutable.{HashMap => MHashMap, Set => MSet}

import ap.parser._
import ap.parser.ITerm
import ap.types.MonoSortedIFunction
import ap.theories._
import ap.api.SimpleAPI
import ap.terfor.conjunctions.Quantifier
import ap.terfor.ConstantTerm

import tricera._
import tricera.concurrency.CallSiteTransform.CallSiteTransforms

trait PointerExpressionChecks {
  def isSelector(func: IFunction) = {
    ADT.Selector.unapply(func).isDefined
  }
}

/**
  * Rewraps Select(q, oldDeref(p)) to oldArrow(p, q)
  * This is the correct thing to do if p is a pointer argument corresponding to an
  * introduced global variable, and the old value of that global variable is what is
  * referenced before it is converted back to a pointer argument.
  *
  * TODO: Handle pointers to nested structures.
  */
 /* Current implementation does not work with nested structures. Currently there is
  * no way to represent something like oldArrow(p, oldArrow(q, r)). Also, representing
  * pointer dereference together with selectors are unclear.
  */
object RewrapPointers
  extends CollectingVisitor[Unit, IExpression]
  with ResultProcessor
  with PointerExpressionChecks {

  override def applyTo(solution: tricera.Solution)
  : Solution = solution match {
    case Solution(functionInvariants, disassociatedLoopInvariants) => 
      Solution(functionInvariants.map(apply), disassociatedLoopInvariants.map(apply))
    case _ =>
      solution
  }

  def apply(funcInvs: FunctionInvariants)
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      PreCondition(preInv),
      PostCondition(postInv),
      loopInvariants) =>
      FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(apply(preInv)),
        PostCondition(apply(postInv)),
        loopInvariants.map(apply))
  }

  def apply(invariant: Invariant): Invariant = invariant match {
    case Invariant(expression, heapInfo, sourceInfo) =>
      Invariant(visit(expression, ()).asInstanceOf[IFormula], heapInfo, sourceInfo)
  }

  def apply(invariant: LoopInvariant): LoopInvariant = invariant match {
    case LoopInvariant(expression, heapInfo, sourceInfo) =>
      LoopInvariant(visit(expression, ()).asInstanceOf[IFormula], heapInfo, sourceInfo)
  }

  override def postVisit(
    t: IExpression,
    dummy: Unit,
    subres: Seq[IExpression])
  : IExpression = t match {
      case IFunApp(func, Seq(IFunApp(ACSLExpression.arrow, args))) if isSelector(func) =>
        IFunApp(ACSLExpression.arrow, Seq(IFunApp(func, args)))
      case IFunApp(func, Seq(IFunApp(ACSLExpression.oldArrow, args))) if isSelector(func) =>
        IFunApp(ACSLExpression.oldArrow, Seq(IFunApp(func, args)))
      case IFunApp(
        func,
        Seq(IFunApp(
          ACSLExpression.deref,
          Seq(ConstantAsProgVarProxy(proxy))))) if isSelector(func) =>
        ACSLExpression.arrowFunApp(ACSLExpression.arrow, proxy, func.asInstanceOf[MonoSortedIFunction])
      case IFunApp(
        func,
        Seq(IFunApp(
          ACSLExpression.oldDeref,
          Seq(ConstantAsProgVarProxy(proxy))))) if isSelector(func) =>
        ACSLExpression.arrowFunApp(ACSLExpression.oldArrow, proxy, func.asInstanceOf[MonoSortedIFunction])
      case _: IExpression => 
        t.update(subres)
    }  
}

/**
  * Maps ProgVarProxies representing introduced global variables to
  * original pointer variables.
  * 
  * A global variable q introduced for a stackpointer argument p will
  * be translated  q`PreExec`Global => p`PreExec`Parameter`Pointer
  */
private object MapProgVarProxies 
  extends CollectingVisitor[MHashMap[String, String], IExpression]{
  def apply(funcInvs: FunctionInvariants, globalIdToParamId: MHashMap[String, String], introducedGlobals: Set[String])
  : FunctionInvariants = funcInvs match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      PreCondition(preInv),
      PostCondition(postInv),
      loopInvariants) =>
      FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(applyTo(preInv, globalIdToParamId, introducedGlobals)),
        PostCondition(applyTo(postInv, globalIdToParamId, introducedGlobals)),
        loopInvariants.map(i => applyTo(i, globalIdToParamId, introducedGlobals)))
  }

  private def applyTo(inv: Invariant, globalIdToParamId: MHashMap[String, String], introducedGlobals: Set[String])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) => 
      Invariant(applyTo(form, globalIdToParamId, introducedGlobals), heapInfo, srcInfo)
  }

  private def applyTo(inv: LoopInvariant, globalIdToParamId: MHashMap[String, String], introducedGlobals: Set[String])
  : LoopInvariant = inv match {
    case LoopInvariant(form, heapInfo, srcInfo) => 
      LoopInvariant(applyTo(form, globalIdToParamId, introducedGlobals), heapInfo, srcInfo)
  }

  private def applyTo(form: IFormula, globalIdToParamId: MHashMap[String, String], introducedGlobals: Set[String]) : IFormula = {
    projectGlobals(visit(form, globalIdToParamId).asInstanceOf[IFormula], introducedGlobals)
  }

  private def projectGlobals(form: IFormula, introducedGlobals: Set[String]): IFormula = {
    // globals introduced for other calls are not inputs of this function
    val constants = SymbolCollector.constants(form)
    val toQuantify = constants.filter {
      case p: ProgVarProxy => p.isGlobal && introducedGlobals(p.name)
      case _ => false
    }
    if (toQuantify.isEmpty) form else {
      // EX g. P(g) & Q is (EX g. P(g)) & Q when Q does not mention g
      val (projected, kept) = LineariseVisitor(form, IBinJunctor.And).partition(f =>
        SymbolCollector.constants(f).exists(toQuantify.contains))
      val remaining = SimpleAPI.withProver { p =>
        p.addConstantsRaw(constants)
        val affected = IExpression.and(projected)
        collectAndAddTheories(p, affected)
        p.simplify(IExpression.quanConsts(Quantifier.EX, toQuantify, affected))
      }
      IExpression.and(kept) &&& remaining
    }
  }

  def collectAndAddTheories(p: SimpleAPI, formula: IFormula) = {
    val theories: Seq[Theory] = {
      val coll = new TheoryCollector
      coll(formula)
      coll.theories
    }
    p.addTheories(theories)
  }
  override def postVisit(
    t: IExpression,
    globalIdToParamId: MHashMap[String, String],
    subres: Seq[IExpression])
  : IExpression = t match {
    case ConstantAsProgVarProxy(proxy) if proxy.isGlobal && globalIdToParamId.contains(proxy.name) =>
        proxy.copy(
          _name = globalIdToParamId(proxy.name),
          _isPointer = true,
          scope = ProgVarProxy.Scope.Parameter)
    case _ => t.update(subres)
  }
  
}

/**
  * Merge contracts from transformed functions into a single contract
  * for the original function.
  */
object MergeTransformedFunctionsContracts {
  def apply(callSiteTransforms: CallSiteTransforms)(result : Result) = {
      (new MergeTransformedFunctionsContracts(callSiteTransforms)(result))
  }
}


private class MergeTransformedFunctionsContracts(callSiteTransforms: CallSiteTransforms)
  extends ResultProcessor {
  override def applyTo(solution: tricera.Solution): Solution = solution match {
    case Solution(functionInvariants, disassociatedLoopInvariants) if !callSiteTransforms.isEmpty => 
      Solution(
        mergeInvariantsOfTransformedFunctions(functionInvariants),
        disassociatedLoopInvariants)
    case _ =>
      solution
  }

  private def mergeInvariantsOfTransformedFunctions(funcInvs: Seq[FunctionInvariants])
  : Seq[FunctionInvariants] = {
    val astAdditions = callSiteTransforms.map(t => t.getAstAdditions()).reduce((a,b) => {a += b})

    val introducedGlobals = astAdditions.introducedGlobalVariables.keySet.toSet
    val originals = astAdditions.transformedFunctionIdToOriginalId
    val transformed = funcInvs.filter(i => originals.contains(i.id))
      .groupBy(i => originals(i.id))

    funcInvs.filterNot(i => originals.contains(i.id)).map { inv =>
      val original = MapProgVarProxies(inv, MHashMap.empty, introducedGlobals)
      transformed.get(original.id) match {
        case None => original
        case Some(variants) =>
          val params = astAdditions.originalFunctionIdToParamterIds(original.id)
          val branches = guardPostcondition(original) +: variants.sortBy(_.id).map { variant =>
            val globals = astAdditions.transformedFunctionIdToParamToGlobal(variant.id)
            val removed = params.filter(globals.contains)
            val cells = globals.values.toSet
            val mapping = astAdditions.globalVariableIdToParameterId
              .filter { case (g, _) => cells(g) }
            val mapped = MapProgVarProxies(variant, mapping, introducedGlobals)
            val branch = derefParameters(mapped, removed.toSet)
            val pointers = removed.map(p => IConstant(ProgVarProxy(p,
              ProgVarProxy.State.PreExec, ProgVarProxy.Scope.Parameter, true)))
            // f(&a, &a) shares one global; f(&a, &b) uses two separate globals
            val aliases = IExpression.and(for (Seq(p, q) <- pointers.combinations(2)) yield
              if (globals(p.c.name) == globals(q.c.name)) p === q
              else IAtom(ACSLExpression.separated, Seq(p, q)))
            val valid = IExpression.and(pointers.map(p => IAtom(ACSLExpression.valid, Seq(p))))
            val postValid = ACSLExpression.validPointers(removed.map(p => ProgVarProxy(p,
              ProgVarProxy.State.PostExec, ProgVarProxy.Scope.Parameter, true)).toSet)
            val oldEntry = derefParameters(mapped.copy(
              postCondition = PostCondition(mapped.preCondition.invariant)),
              removed.toSet).postCondition.invariant.expression
            branch.copy(
              preCondition = PreCondition(branch.preCondition.invariant.copy(
                expression = branch.preCondition.invariant.expression &&& aliases &&& valid)),
              postCondition = PostCondition(branch.postCondition.invariant.copy(
                expression = (aliases &&& oldEntry) ===>
                  (branch.postCondition.invariant.expression &&& postValid))))
          }
          mergeBranches(original, branches)
      }
    }
  }

  private def guardPostcondition(inv: FunctionInvariants): FunctionInvariants =
    inv.copy(postCondition = PostCondition(inv.postCondition.invariant.copy(
      expression = inv.preCondition.invariant.expression ===> inv.postCondition.invariant.expression)))

  private def mergeBranches(original: FunctionInvariants,
                             branches: Seq[FunctionInvariants]): FunctionInvariants = {
    // each postcondition is already guarded by its variant's entry conditions
    // use the same constants for each occurrence of a source variable
    val constants = branches.flatMap(b => SymbolCollector.constants(
      b.preCondition.invariant.expression & b.postCondition.invariant.expression))
    val common = constants.groupBy(_.toString).values.flatMap { group =>
      group.map(c => c -> IConstant(group.head))
    }.toMap
    def rename(f: IFormula) = ConstantSubstVisitor(f, common)
    original.copy(
      preCondition = PreCondition(original.preCondition.invariant.copy(expression =
        IExpression.connectSimplify(branches.map(b => rename(b.preCondition.invariant.expression)), IBinJunctor.Or))),
      postCondition = PostCondition(original.postCondition.invariant.copy(expression =
        IExpression.connectSimplify(branches.map(b => rename(b.postCondition.invariant.expression)), IBinJunctor.And))),
      loopInvariants = branches.flatMap(_.loopInvariants).toList)
  }

  private def derefParameters(inv: FunctionInvariants,
                              params: Set[String]): FunctionInvariants = {
    def deref(form: IFormula, post: Boolean): IFormula = {
      val replacements = SymbolCollector.constants(form).collect {
        case p: ProgVarProxy if p.isParameter && params(p.name) =>
          val fun = if (post && p.isPreExec) ACSLExpression.oldDeref else ACSLExpression.deref
          (p: ConstantTerm) -> ACSLExpression.derefFunApp(fun, p)
      }.toMap
      ConstantSubstVisitor(form, replacements)
    }
    inv.copy(
      preCondition = PreCondition(inv.preCondition.invariant.copy(
        expression = deref(inv.preCondition.invariant.expression, false))),
      postCondition = PostCondition(inv.postCondition.invariant.copy(
        expression = deref(inv.postCondition.invariant.expression, true))))
  }

}

/**
  * Adds valid pointer requirements to preconditions.
  */
object AddValidPointerPredicates 
  extends CollectingVisitor[Unit, (MSet[ProgVarProxy], MSet[ProgVarProxy])]
  with ResultProcessor {
  override def applyTo(solution: tricera.Solution): Solution = solution match {
    case Solution(functionInvariants, disassociatedLoopInvariants) =>
        Solution(functionInvariants.map(applyTo), disassociatedLoopInvariants)
      case _ => solution
  }

  private def applyTo(funcInv: FunctionInvariants)
  : FunctionInvariants = funcInv match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      PreCondition(preInv),
      PostCondition(postInv),
      loopInvariants) =>
      FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(
          applyTo(preInv)
        ),
        PostCondition(postInv),
        loopInvariants)
  }

  private def applyTo(inv: Invariant)
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) =>
      val (found, existing) = visit(form, ())
      val (keep, extra) = found.partition(p => p.isPreExec)
      extra.foreach(e => keep.find(k => k.name == e.name) match {
        case None => keep += e
        case _ => ()
      })
      existing.foreach(e => keep.find(k => k.name == e.name) match {
        case Some(i) => keep -= i
        case _ => ()
      })

      Invariant(
        form &&& ACSLExpression.validPointers(keep.toSet).asInstanceOf[IFormula],
        heapInfo,
        srcInfo)
  }
  
  override def postVisit(
    t: IExpression,
    dummy: Unit,
    subres: Seq[(MSet[ProgVarProxy], MSet[ProgVarProxy])])
  : (MSet[ProgVarProxy], MSet[ProgVarProxy]) = t match {
    case IAtom(pred, Seq(ConstantAsProgVarProxy(proxy))) if (pred == ACSLExpression.valid) =>
      (MSet(), MSet(proxy))
    case ConstantAsProgVarProxy(proxy) if proxy.isPointer && proxy.isParameter =>
      (MSet(proxy), MSet())
    case _ if subres.nonEmpty => 
      subres.reduce((a,b) => (a._1 ++ b._1, a._2 ++ b._2))
    case _ => (MSet(), MSet())
  }
}
