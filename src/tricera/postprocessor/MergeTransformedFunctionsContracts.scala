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
    case Solution(functionInvariants) => 
      Solution(functionInvariants.map(apply))
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
  extends CollectingVisitor[(MHashMap[String, String], MSet[ProgVarProxy]), IExpression]
  with PointerExpressionChecks{

  def apply(form: IExpression, nameMap: MHashMap[String, String], foundPointers: MSet[ProgVarProxy]) = {
    visit(form, (nameMap, foundPointers)).asInstanceOf[IFormula]
  }

  override def postVisit(
    t: IExpression,
    nameMapAndPtrs: (MHashMap[String,String], MSet[ProgVarProxy]),
    subres: Seq[IExpression])
  : IExpression = (t, subres) match {
      case (ConstantAsProgVarProxy(proxy), _) if nameMapAndPtrs._1.get(proxy.name).isDefined =>
        val (transformedToOriginalId, foundPointers) = nameMapAndPtrs
        foundPointers += proxy.copy(_name = transformedToOriginalId(proxy.name), _isPointer = true)
        ACSLExpression.derefFunApp(
          ACSLExpression.deref,
          proxy.copy(_name = transformedToOriginalId(proxy.name), _isPointer = true))
      case _ => 
        RewrapPointers.postVisit(t, (), subres)
    }
}


private object MapPostCondProgVarProxies
  extends CollectingVisitor[(MHashMap[String, String], MSet[ProgVarProxy]), IExpression] {
  def apply(form: IExpression, nameMap: MHashMap[String, String], validPointers: MSet[ProgVarProxy]) = {
    visit(form, (nameMap, validPointers)).asInstanceOf[IFormula]  
  }

  override def postVisit(
    t: IExpression,
    nameMapAndPtrs: (MHashMap[String,String], MSet[ProgVarProxy]),
    subres: Seq[IExpression])
  : IExpression = t match {
      case ConstantAsProgVarProxy(proxy) if nameMapAndPtrs._1.get(proxy.name).isDefined =>
        val (transformedToOriginalId, foundPointers) = nameMapAndPtrs
        foundPointers += proxy.copy(_name = transformedToOriginalId(proxy.name), _isPointer = true)
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
  def apply(funcInvs: FunctionInvariants, nameMap: MHashMap[String, String], foundPointers: MSet[ProgVarProxy])
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
        PreCondition(applyToPre(preInv, nameMap, foundPointers)),
        PostCondition(applyToPost(postInv, nameMap, foundPointers)),
        loopInvariants.map(i => applyTo(i, nameMap, foundPointers)))
  }

  private def applyToPre(inv: Invariant, nameMap: MHashMap[String, String], foundPointers: MSet[ProgVarProxy])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) => 
      Invariant(MapPreCondProgVarProxies(form, nameMap, foundPointers).asInstanceOf[IFormula], heapInfo, srcInfo)
  }

  private def applyToPost(inv: Invariant, nameMap: MHashMap[String, String], foundPointers: MSet[ProgVarProxy])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) => 
      Invariant(MapPostCondProgVarProxies(form, nameMap, foundPointers).asInstanceOf[IFormula], heapInfo, srcInfo)
  }

  private def applyTo(inv: LoopInvariant, nameMap: MHashMap[String, String], foundPointers: MSet[ProgVarProxy])
  : LoopInvariant = inv match {
    case LoopInvariant(form, heapInfo, srcInfo) => 
      LoopInvariant(MapPreCondProgVarProxies(form, nameMap, foundPointers).asInstanceOf[IFormula], heapInfo, srcInfo)
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
    case Solution(functionInvariants) if !callSiteTransforms.isEmpty => 
      Solution(mergeInvariantsOfTransformedFunctions(functionInvariants))
    case _ =>
      solution
  }

  private def addValidPointerAtoms(inv: Invariant, pointers: MSet[ProgVarProxy])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) =>
      Invariant(
        form &&& ACSLExpression.validPointers(pointers.toSet).asInstanceOf[IFormula],
        heapInfo,
        srcInfo)
  }

  private def addValidPointerAtoms(invs: FunctionInvariants, pointers: MSet[ProgVarProxy])
  : FunctionInvariants = invs match {
      case FunctionInvariants(
        id, isSrcAnnotated,
        PreCondition(preInv),
        PostCondition(postInv),
        loopInvariants) =>
          FunctionInvariants(
            id,
            isSrcAnnotated,
            PreCondition(addValidPointerAtoms(preInv, pointers)),
            PostCondition(addValidPointerAtoms(postInv, pointers)),
            loopInvariants)
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
      val foundPointers = MSet[ProgVarProxy]()
      val invs = transformedFuncInvs.fold(funcInvs.find(i => i.id == originalId).get)(
        (original, transformed) => 
          original.meet(MapProgVarProxies(transformed, astAdditions.globalVariableIdToParameterId, foundPointers)))
//      val (prePointers, postPointers) = foundPointers.partition(p => p.isPreExec)
//      postPointers.foreach(p => prePointers.find(i => i.name == p.name) match {
//        case None => prePointers += p
//        case _ => ()
//      })
//      addValidPointerAtoms(invs, prePointers)
      invs
    }}).toSeq
  }
}

/**
  * Scans the invariants for ProgVarProxy instances and adds a valid pointer atom
  * for each one.
  */
object AddValidPointerAtoms 
  extends CollectingVisitor[Unit, MSet[ProgVarProxy]]
  with ResultProcessor {
  override def applyTo(solution: tricera.Solution): Solution = solution match {
    case Solution(functionInvariants) =>
        Solution(functionInvariants.map(applyTo))
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
        PreCondition(applyTo(preInv)),
        PostCondition(applyTo(postInv)),
        loopInvariants)
  }

  private def applyTo(inv: Invariant)
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) =>
      val (keep, extra) = visit(form, ()).partition(p => p.isPreExec)
      extra.foreach(e => keep.find(k => k.name == e.name) match {
        case None => keep += e
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
    subres: Seq[MSet[ProgVarProxy]])
  : MSet[ProgVarProxy] = t match {
    case ConstantAsProgVarProxy(proxy) if proxy.isPointer => MSet(proxy)
    case _ if subres.nonEmpty => subres.reduce((a,b) => a ++ b)
    case _ => MSet()
  }
}
