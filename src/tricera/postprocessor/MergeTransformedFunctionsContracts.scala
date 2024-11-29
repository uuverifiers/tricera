package tricera.postprocessor

import scala.collection.mutable.{HashMap => MHashMap, MutableList, Buffer, ArrayBuffer}

import ap.parser.{IFormula, VariablePermVisitor, IVarShift}
import ap.terfor.preds.Predicate
import tricera.concurrency.CallSiteTransform.CallSiteTransforms
import tricera.concurrency.CallSiteTransform
import tricera.postprocessor.SolutionProcessor.Solution
import tricera.concurrency.CCReader
import ap.parser.Environment.Constant
import ap.parser.Environment.Variable
import _root_.ap.parser.IBoolLit
import tricera.concurrency.ccreader.CCVar

import tricera.Util.printlnDebug

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
      val ctxArgNameToIndex = targetCtx.prePred.argVars.map(v => v.name).zipWithIndex.toMap

      printlnDebug("# mapTo 1 ############################################")
      for ((key, value) <- prePredArgIndexToName) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }
      
      printlnDebug("# mapTo 2 ############################################")
      for ((key, value) <- ctxArgNameToIndex) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }

      for ((ix, name) <- prePredArgIndexToName) {
        val p = lookup(name)
        ctxArgNameToIndex.get(lookup(name)) match {
          case Some(i) => printlnDebug(f"${ix} -> name: ${name} -> param: ${p} -> ${i}")
          case None => assert(false, f"Missing predicate argument ${p}")
        }
      }

      val predVarShifts = funcContext.prePred.argVars
        .zipWithIndex
        .map({ case (v, i) => ctxArgNameToIndex(lookup(v.name))-i })
        .toList

      predVarShifts.foreach(i => printlnDebug(f"diff: ${i}"))

      VariablePermVisitor(pre, IVarShift(predVarShifts, 0))
    }

    def mapPostPredVars() = {
      val ctxArgNameToIndex = targetCtx.postPred.argVars.map(v => v.name).zipWithIndex.toMap


      printlnDebug("# mapTo 3 ############################################")
      for ((key, value) <- postPredArgIndexToName) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }
      
      printlnDebug("# mapTo 4 ############################################")
      for ((key, value) <- ctxArgNameToIndex) {
          printlnDebug(f"key: ${key} -> value: ${value}")
      }

      for ((ix, name) <- postPredArgIndexToName) {
        val p = lookup(name)
        ctxArgNameToIndex.get(lookup(name)) match {
          case Some(i) => printlnDebug(f"${ix} -> name: ${name} -> param: ${p} -> ${i}")
          case None => ctxArgNameToIndex.get(lookupOld(name)) match {
            case Some(i) => printlnDebug(f"${ix} -> name: ${name} -> param: ${p} -> ${i}")
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

      VariablePermVisitor(pre, IVarShift(predVarShifts, 0))
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
    val newPrePredFormula = pre ||| other.pre
    val newPostPredFormula = (pre ===> post) &&& (other.pre ===> other.post)
    new MergableContract(funcContext, newPrePredFormula, newPostPredFormula)
  }
}

object MergeTransformedFunctionsContracts {
  def apply(
    callSiteTransforms: CallSiteTransforms,
    contexts: Map[String, CCReader.FunctionContext],
    solution : Solution) = {
      (new MergeTransformedFunctionsContracts(callSiteTransforms, contexts, solution)).apply()
  }
}

class MergeTransformedFunctionsContracts(
    callSiteTransforms: CallSiteTransforms,
    functionContexts: Map[String,CCReader.FunctionContext],
    solution : Solution) {

  def apply(): (Solution, Map[String,CCReader.FunctionContext]) = {
    def isAssociatedWithTransformedFunction(pred: Predicate) = {
      functionContexts.exists({ case (funcName, ctx) => ctx.prePred.pred == pred || ctx.postPred.pred == pred })
    }

    def toContract(context: CCReader.FunctionContext, solution: SolutionProcessor.Solution) = {
      MergableContract(context, solution(context.prePred.pred), solution(context.postPred.pred))
    }

    val astAdditions = callSiteTransforms.map(t => t.getAstAdditions()).reduce((a,b) => {a += b})

    val contractsByOriginalFuncId = astAdditions.transformedFunctionIdToOriginalId
      .groupBy({case (transformedId, origId) => origId })
      .mapValues(_.keySet.map(funcId => toContract(functionContexts(funcId), solution)))

    var mergedSolution = solution.filter({case (pred, formula) => !isAssociatedWithTransformedFunction(pred)})

    for ((originalId, contracts) <- contractsByOriginalFuncId) {
      val fullContract = 
        contracts.fold(toContract(functionContexts(originalId), solution))(
            (original, transformed) => 
                original.meet(transformed.mapTo(original.funcContext, astAdditions.globalVariableIdToParameterId)))

      mergedSolution = 
        mergedSolution + 
        (fullContract.funcContext.prePred.pred -> fullContract.pre) +
        (fullContract.funcContext.postPred.pred -> fullContract.post)
    }
    (mergedSolution, functionContexts.filterKeys(funcId => contractsByOriginalFuncId.contains(funcId)))
  }
}
