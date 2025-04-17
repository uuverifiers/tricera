package tricera.postprocessor

import scala.collection.mutable.{HashMap => MHashMap, Set => MSet, Buffer, ArrayBuffer}

import ap.parser.IFormula
import ap.parser.CollectingVisitor
import ap.parser.IExpression
import ap.parser.IConstant
import ap.parser.IFunApp
import ap.parser.IFunction

import ap.theories.ADT
import ap.types.MonoSortedIFunction

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
  extends CollectingVisitor[MHashMap[String, String], IExpression]
  with PointerExpressionChecks{

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
          proxy.copy(_name = transformedToOriginalId(proxy.name), _isPointer = true))
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
          proxy.copy(_name = transformedToOriginalId(proxy.name), _isPointer = true))
      case _: IExpression => 
        RewrapPointers.postVisit(t, (), subres)
    }
}


/**
  * Maps ProgVarProxies representing introduced global variables to
  * original pointer variables.
  * 
  * A global variable q introduced for a stackpointer argument p will
  * be translated in different ways depending on if they occur in
  * a pre-condition or a post-condition.
  * 
  * Pre-condition mapping:
  * q`PreExec => deref(p`PreExec)
  * 
  * Post-condition mapping:
  * q`PreExec => oldDeref(p`PreExec)
  * q`PostExec => deref(p`PostExec),
  */
private object MapProgVarProxies {
  def apply(funcInvs: FunctionInvariants, nameMap: MHashMap[String, String])
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
        PreCondition(applyToPre(preInv, nameMap)),
        PostCondition(applyToPost(postInv, nameMap)),
        loopInvariants.map(i => applyTo(i, nameMap)))
  }

  private def applyToPre(inv: Invariant, nameMap: MHashMap[String, String])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) => 
      Invariant(MapPreCondProgVarProxies(form, nameMap).asInstanceOf[IFormula], heapInfo, srcInfo)
  }

  private def applyToPost(inv: Invariant, nameMap: MHashMap[String, String])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) => 
      Invariant(MapPostCondProgVarProxies(form, nameMap).asInstanceOf[IFormula], heapInfo, srcInfo)
  }

  private def applyTo(inv: LoopInvariant, nameMap: MHashMap[String, String])
  : LoopInvariant = inv match {
    case LoopInvariant(form, heapInfo, srcInfo) => 
      LoopInvariant(MapPreCondProgVarProxies(form, nameMap).asInstanceOf[IFormula], heapInfo, srcInfo)
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
      transformedFuncInvs.fold(funcInvs.find(i => i.id == originalId).get)(
        (original, transformed) => 
          original.meet(MapProgVarProxies(transformed, astAdditions.globalVariableIdToParameterId)))
    }}).toSeq
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
    case ConstantAsProgVarProxy(proxy) if proxy.isPointer =>
      (MSet(proxy), MSet())
    case _ if subres.nonEmpty => 
      subres.reduce((a,b) => (a._1 ++ b._1, a._2 ++ b._2))
    case _ => (MSet(), MSet())
  }
}
