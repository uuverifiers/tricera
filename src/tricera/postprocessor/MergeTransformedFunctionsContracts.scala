package tricera.postprocessor

import scala.collection.mutable.{HashMap => MHashMap, Set => MSet, Buffer, ArrayBuffer}

import ap.parser.IFormula
import ap.parser.CollectingVisitor
import ap.parser.IExpression
import ap.parser.IConstant
import ap.parser.IFunApp
import ap.parser.IFunction

//import ap.theories.ADT
import ap.types.MonoSortedIFunction
import ap.theories._
//import ap.SimpleAPI

import tricera.concurrency.CallSiteTransform.CallSiteTransforms
import tricera.concurrency.CallSiteTransform
import tricera.concurrency.CCReader
import tricera.concurrency.ccreader.CCVar

import tricera.{
  ConstantAsProgVarProxy, FunctionInvariants, Invariant, InvariantContext,
  LoopInvariant, PostCondition, PreCondition, ProgVarProxy,
  Result, Solution}
import ap.parser.IAtom
import tricera.Util.printlnDebug
import ap.api.SimpleAPI
import ap.parser.SymbolCollector
import ap.terfor.conjunctions.Quantifier
import ap.parser.ConstantSubstVisitor
import ap.terfor.ConstantTerm
import ap.parser.ITerm

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


private object MapPreCondProgVarProxies 
  extends CollectingVisitor[MHashMap[String, String], IExpression]  {

  def apply(form: IExpression, nameMap: MHashMap[String, String]) = {
    visit(form, nameMap).asInstanceOf[IFormula]
  }

  override def postVisit(
    t: IExpression,
    transformedToOriginalId: MHashMap[String, String],
    subres: Seq[IExpression])
  : IExpression = (t, subres) match {
      case (ConstantAsProgVarProxy(proxy), _) if transformedToOriginalId.get(proxy.name).isDefined =>
        ACSLExpression.derefFunApp(
          ACSLExpression.deref,
          proxy.copy(
            _name = transformedToOriginalId(proxy.name),
            _isPointer = true,
            scope = ProgVarProxy.Scope.Parameter))
      case _ => 
        RewrapPointers.postVisit(t, (), subres)
    }
}


private object MapPostCondProgVarProxies
  extends CollectingVisitor[MHashMap[String, String], IExpression] {
  def apply(form: IExpression, nameMap: MHashMap[String, String]) = {
    visit(form, nameMap).asInstanceOf[IFormula]  
  }

  override def postVisit(
    t: IExpression,
    transformedToOriginalId: MHashMap[String, String],
    subres: Seq[IExpression])
  : IExpression = t match {
      case ConstantAsProgVarProxy(proxy) if transformedToOriginalId.get(proxy.name).isDefined =>
        val derefFun = 
          if (proxy.isPreExec) {
            ACSLExpression.oldDeref
          } else {
            ACSLExpression.deref
          }
        ACSLExpression.derefFunApp(
          derefFun, 
          proxy.copy(
            _name = transformedToOriginalId(proxy.name),
            _isPointer = true,
            scope = ProgVarProxy.Scope.Parameter))
      case _: IExpression => 
        RewrapPointers.postVisit(t, (), subres)
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
  def apply(funcInvs: FunctionInvariants, globalIdToParamId: MHashMap[String, String], funcParamIds: List[String])
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
        PreCondition(applyTo(preInv, globalIdToParamId, funcParamIds)),
        PostCondition(applyTo(postInv, globalIdToParamId, funcParamIds)),
        loopInvariants.map(i => applyTo(i, globalIdToParamId, funcParamIds)))
  }

  private def applyTo(inv: Invariant, globalIdToParamId: MHashMap[String, String], funcParamIds: List[String])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) => 
      Invariant(applyTo(form, globalIdToParamId, funcParamIds), heapInfo, srcInfo)
  }

  private def applyTo(inv: LoopInvariant, globalIdToParamId: MHashMap[String, String], funcParamIds: List[String])
  : LoopInvariant = inv match {
    case LoopInvariant(form, heapInfo, srcInfo) => 
      LoopInvariant(applyTo(form, globalIdToParamId, funcParamIds), heapInfo, srcInfo)
  }

  private def applyTo(form: IFormula, globalIdToParamId: MHashMap[String, String], funcParamIds: List[String]) : IFormula = {
    exQuantifyFalseParameters(visit(form, globalIdToParamId).asInstanceOf[IFormula], funcParamIds)
  }

  private def exQuantifyFalseParameters(form: IFormula, funcParamIds: List[String]) : IFormula = {
    // Some of the introduced global variables for paramters to other functions
    // may be used in conditions on the parameters of the current function.
    // Since these variables are not true global variables, they cannot affect
    // the conditions for the current function. We account for that by existentially
    // quantifying over the introduced variables that are not parameters to the current
    // function.
    printlnDebug(s"before EX quantify: ${form}")
    SimpleAPI.withProver{ p =>
      val constants = SymbolCollector.constants(form)
      p.addConstantsRaw(constants)
//      p.addRelations(ACSLExpression.predicates)
//      ACSLExpression.functions.foreach(f => p.addFunction(f))
      collectAndAddTheories(p, form)
      val toQuantify = constants
        .filter({case c: ProgVarProxy => c.isParameter && !funcParamIds.contains(c.name)})
      val projected = IExpression.quanConsts(Quantifier.EX, toQuantify, form)
      val simplified = p.simplify(projected)
      printlnDebug(s"after EX quantify: ${simplified}")
      simplified
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
    case ConstantAsProgVarProxy(proxy) if globalIdToParamId.get(proxy.name).isDefined =>
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

    val transformedFuncInvsByOriginalId = astAdditions.transformedFunctionIdToOriginalId
      .groupBy({case (transformedId, origId) => origId })
      .mapValues(_.keySet
        .map(funcId => funcInvs.find(i => i.id == funcId))
        // Due to inlining of functions without annotations, not all transformed
        // functions have a corresponding FunctionInvariants instance.
        .withFilter(o => o.isDefined)
        .map(o => o.get))
      .filter({ case (id, set) => !set.isEmpty})

    transformedFuncInvsByOriginalId.map({case (originalId, transformedFuncInvs) => {
      (originalId,
       transformedFuncInvs.fold(funcInvs.find(i => i.id == originalId).get)(
        (original, transformed) => 
          original.meet(
            MapProgVarProxies(
              transformed,
              astAdditions.globalVariableIdToParameterId,
              astAdditions.originalFunctionIdToParamterIds(originalId)))))
    }})
//    .map({ case (id, funcInv) => exQuantifyIntroducedGlobals(astAdditions.originalFunctionIdToParamterIds(id), funcInv)})
    .map({ case (id, funcInv) => derefParameters(funcInv, astAdditions.originalFunctionIdToParamterIds(id)) })
    .toSeq
  }

  private def derefParameters(funcInv: FunctionInvariants, funcParamsIds: List[String]): FunctionInvariants = funcInv match {
    case FunctionInvariants(
      id,
      isSrcAnnotated,
      PreCondition(preCondition),
      PostCondition(postCondition),
      loopInvariants) => 
        val preDerefMap = 
          SymbolCollector.constants(preCondition.expression)
            .filter(c => funcParamsIds.exists(p => p == c.name))
            .filter({ case c: ProgVarProxy if c.isPreExec => true})
            .map(c => (c, ACSLExpression.derefFunApp(ACSLExpression.deref, c.asInstanceOf[ProgVarProxy])))
            .toMap
        val postDerefMap =
          SymbolCollector.constants(postCondition.expression)
            .withFilter(c => funcParamsIds.exists(p => p == c.name))
            .withFilter({ case c: ProgVarProxy => true})
            .map({ 
              case c: ProgVarProxy if c.isPreExec => 
                (c.asInstanceOf[ConstantTerm], ACSLExpression.derefFunApp(ACSLExpression.oldDeref, c))
              case c: ProgVarProxy => 
                (c.asInstanceOf[ConstantTerm], ACSLExpression.derefFunApp(ACSLExpression.deref, c))})
            .toMap
      FunctionInvariants(
        id,
        isSrcAnnotated,
        PreCondition(derefParameters(preCondition, preDerefMap)),
        PostCondition(derefParameters(postCondition, postDerefMap)),
        loopInvariants)
  }

  private def derefParameters(invariant: Invariant, derefMap: Map[ConstantTerm, ITerm]): Invariant = invariant match {
    case Invariant(form, heapInfo, sourceInfo) => 
      Invariant(ConstantSubstVisitor(form, derefMap), heapInfo, sourceInfo)
  }

  private def exQuantifyIntroducedGlobals(
    paramIds: List[String],
    funcInv: FunctionInvariants)
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
        PreCondition(exQuantifyIntroducedGlobals(paramIds, preInv)),
        PostCondition(exQuantifyIntroducedGlobals(paramIds, postInv)),
        loopInvariants)
  }

  def collectAndAddTheories(p: SimpleAPI, formula: IFormula) = {
    val theories: Seq[Theory] = {
      val coll = new TheoryCollector
      coll(formula)
      coll.theories
    }
    p.addTheories(theories)
  }

  private def exQuantifyIntroducedGlobals(
    paramIds: List[String],
    inv: Invariant)
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) =>
      val p = SimpleAPI.spawn
      p.addConstantsRaw(SymbolCollector.constants(form))
      p.addRelations(ACSLExpression.predicates)
      ACSLExpression.functions.foreach(f => p.addFunction(f))
      collectAndAddTheories(p, form)
      val toKeep = SymbolCollector
        .constants(form)
        .filter(c => paramIds.contains(c.name) || heapInfo.map(i => i.heapTermName == c.name).getOrElse(false))
        .map(IConstant)
      val projected = p.projectEx(form, toKeep)
      val simplified = p.simplify(projected)
      Invariant(simplified, heapInfo, srcInfo)
  }
}


private class DerefParameters()
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
  * Scans the invariants for ProgVarProxy instances and adds a valid pointer atom
  * for each one that is a pointer.
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
        PostCondition(
          applyTo(postInv)
        ),
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
