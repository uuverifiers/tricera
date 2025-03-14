package tricera.postprocessor

import scala.collection.mutable.{HashMap => MHashMap, MutableList, Buffer, ArrayBuffer}

import ap.parser.{IFormula, VariablePermVisitor, IVarShift}
import ap.terfor.preds.Predicate
import tricera.concurrency.CallSiteTransform.CallSiteTransforms
import tricera.concurrency.CallSiteTransform
import tricera.Solution
import tricera.concurrency.CCReader
import ap.parser.Environment.Constant
import ap.parser.Environment.Variable
import _root_.ap.parser.IBoolLit
import tricera.concurrency.ccreader.CCVar

import tricera.Util.printlnDebug
import tricera.Result
import tricera.FunctionInvariants
import ap.parser.CollectingVisitor
import ap.parser.IExpression
import tricera.{
  ConstantAsProgVarProxy, Invariant, InvariantContext,
  LoopInvariant, PostCondition, PreCondition, ProgVarProxy}
import ap.parser.IConstant

private object MergableContract {
  def apply(
    funcContext: CCReader.FunctionContext,
    pre: IFormula,
    post: IFormula) = {
        new MergableContract(funcContext, pre, post)
    }
}

private class MergableContract(
    val funcContext: CCReader.FunctionContext,
    val pre: IFormula,
    val post: IFormula) {

  private var prePredArgIndexToName = 
    funcContext.prePred.argVars.zipWithIndex.map({ case (v, i) => (i, v.name) }).toMap

  private var postPredArgIndexToName = 
    funcContext.postPred.argVars.zipWithIndex.map({ case (v, i) => (i, v.name) }).toMap

  private var postPredArgNameToIndex = 
    funcContext.postPred.argVars.zipWithIndex.map({ case (v, i) => (v.name, i) }).toMap

  /**
    * Map contract from one function context to another.
    * 
    * @param targetCtx Function context to map to.
    * @param globalToParam Global variables that should be mapped to parameters.
    */
  def mapTo(targetCtx: CCReader.FunctionContext, globalToParam: MHashMap[String, String]): MergableContract = {
    def lookup(name: String) = {
      // suffix can be either _old or _post depending on if we are
      // looking for a variable representing the pre or post state
      // value of things.
      val suffix = name.substring(name.lastIndexOf("_"))
      val nameNoSuffix = name.stripSuffix(suffix)
      globalToParam.getOrElse(nameNoSuffix, nameNoSuffix) + suffix
    }

    def lookupOld(name: String) = {
      val suffix = name.substring(name.lastIndexOf("_"))
      val nameNoSuffix = name.stripSuffix(suffix)
      globalToParam.getOrElse(nameNoSuffix, nameNoSuffix) + "_old"
    }

    def mapPrePredVars() = {
      val targetCtxArgNameToIndex = targetCtx.prePred.argVars.map(v => v.name).zipWithIndex.toMap

      printlnDebug("# prePred: prePredArgIndexToName ############################################")
      for ((key, value) <- prePredArgIndexToName) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }
      
      printlnDebug("# prePred: targetCtxArgNameToIndex mapTo 2 ############################################")
      for ((key, value) <- targetCtxArgNameToIndex) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }

      for ((ix, name) <- prePredArgIndexToName) {
        val p = lookup(name)
        targetCtxArgNameToIndex.get(lookup(name)) match {
          case Some(i) => printlnDebug(f"${ix} -> name: ${name} -> param: ${p} -> ${i}")
          case None => assert(false, f"Missing predicate argument ${p}")
        }
      }

      val predVarShifts = funcContext.prePred.argVars
        .zipWithIndex
        .map({ case (v, i) => targetCtxArgNameToIndex(lookup(v.name))-i })
        .toList

      predVarShifts.foreach(i => printlnDebug(f"diff: ${i}"))

      VariablePermVisitor(pre, IVarShift(predVarShifts, 0))
    }

    def mapPostPredVars() = {
      val ctxArgNameToIndex = targetCtx.postPred.argVars.map(v => v.name).zipWithIndex.toMap


      printlnDebug("# postPred: postPredArgIndexToName mapTo 3 ############################################")
      for ((key, value) <- postPredArgIndexToName) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }
      
      printlnDebug("# postPred: ctxArgNameToIndex mapTo 4 ############################################")
      for ((key, value) <- ctxArgNameToIndex) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }

      for ((ix, name) <- postPredArgIndexToName) {
        val p = lookup(name)
        ctxArgNameToIndex.get(lookup(name)) match {
          case Some(i) => printlnDebug(f"${ix} -> name: ${name} -> param: ${p} -> ${i}")
          case None => ctxArgNameToIndex.get(lookupOld(name)) match {
            case Some(i) => printlnDebug(f"${ix} -> name: ${name} -> param: ${lookupOld(name)} -> ${i}")
            case None => assert(false, f"Missing predicate argument ${p}")
          }
        }
      }

      val predVarShifts = funcContext.postPred.argVars
        .zipWithIndex
        .map({ case (v, i) => 
            ctxArgNameToIndex.getOrElse(lookup(v.name),
              ctxArgNameToIndex(lookupOld(v.name)))-i })
        .toList

      predVarShifts.foreach(i => printlnDebug(f"diff: ${i}"))

      VariablePermVisitor(post, IVarShift(predVarShifts, 0))
    }
    
    MergableContract(funcContext, mapPrePredVars(), mapPostPredVars())
  }

  /**
   * Assumes that this contract and "other" refer to the same 
   * [[FunctionContext]].
   * 
   * @param other Contract to meet with
   */
  def meet(other: MergableContract): MergableContract = {
    val preToPostIndexShifts = 
      prePredArgIndexToName
        .mapValues(name => postPredArgNameToIndex(name))
        .toList.map({ case (preIndex, postIndex) => postIndex - preIndex})

    printlnDebug("# meet #########################")
    printlnDebug("Pre index to name:")
    for ((index, name) <- prePredArgIndexToName) {
      printlnDebug(f"${index} -> ${name}")
    }
    printlnDebug("Post name to index:")
    for ((name, index) <- postPredArgNameToIndex) {
      printlnDebug(f"${name} -> ${index}")
    }
    printlnDebug(f"Shift list: ${preToPostIndexShifts.toString()}")
    
//    for (shift <- preToPostIndexShifts) {
//      printlnDebug(f"")
//    }

    def preToPostIndex(formula: IFormula) = {
      VariablePermVisitor(formula, IVarShift(preToPostIndexShifts, 0))
    }

    val newPrePredFormula = pre ||| other.pre
    val newPostPredFormula = 
      (preToPostIndex(pre) ===> post) &&& (preToPostIndex(other.pre) ===> other.post)
    printlnDebug(f"PRE: ${pre.toString} ||| ${other.pre} = ${newPrePredFormula.toString}")
    printlnDebug(f"POST ${(preToPostIndex(pre) ==> post).toString()} & ${(preToPostIndex(other.pre) ==> other.post)} = ${newPostPredFormula.toString}")
    new MergableContract(funcContext, newPrePredFormula, newPostPredFormula)
  }
}

object MergeTransformedFunctionsContracts {
  def apply(callSiteTransforms: CallSiteTransforms)(result : Result) = {
      (new MergeTransformedFunctionsContracts(callSiteTransforms)(result))
  }
}

private object RenameProgVarProxies extends CollectingVisitor[MHashMap[String, String], IExpression] {
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
        PreCondition(applyTo(preInv, nameMap)),
        PostCondition(applyTo(postInv, nameMap)),
        loopInvariants.map(i => applyTo(i, nameMap)))
  }

  private def applyTo(inv: Invariant, nameMap: MHashMap[String, String])
  : Invariant = inv match {
    case Invariant(form, heapInfo, srcInfo) => 
      Invariant(visit(form, nameMap).asInstanceOf[IFormula], heapInfo, srcInfo)
  }

  private def applyTo(inv: LoopInvariant, nameMap: MHashMap[String, String])
  : LoopInvariant = inv match {
    case LoopInvariant(form, heapInfo, srcInfo) => 
      LoopInvariant(visit(form, nameMap).asInstanceOf[IFormula], heapInfo, srcInfo)
  }


  override def postVisit(
    t: IExpression,
    transformedToOriginalId: MHashMap[String,String],
    subres: Seq[IExpression])
  : IExpression = t match {
      case ConstantAsProgVarProxy(proxy) if transformedToOriginalId.get(proxy.name).isDefined =>
        IConstant(proxy.copy(_name = transformedToOriginalId(proxy.name), _isPointer = true))
      case _: IExpression => 
        t.update(subres)
    }
}

private class MergeTransformedFunctionsContracts(callSiteTransforms: CallSiteTransforms) extends ResultProcessor {
  override def applyTo(solution: tricera.Solution): Solution = solution match {
    case Solution(functionInvariants) if !callSiteTransforms.isEmpty => 
      Solution(mergeInvariantsOfTransformedFunctions(functionInvariants))
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
          original.meet(RenameProgVarProxies(transformed, astAdditions.globalVariableIdToParameterId)))
    }}).toSeq
  }
}
