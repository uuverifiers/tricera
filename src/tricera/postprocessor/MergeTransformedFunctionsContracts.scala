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

  def mapTo(targetCtx: CCReader.FunctionContext, globalToParam: MHashMap[String, String]): MergableContract = {
    /*
      For each variable index in pre/post condition map it to corresponding index in ctx.pre/post:
        1. index => name, globalToParam(name) => ctx.index

      use VariablePermVisitor
      or  VariableSubstVisitor
    */
    def lookup(name: String) = {
      // suffix can be either _old or _post depending on if we are
      // looking for a variable representing the pre or post state
      // value of things.
      val suffix = name.substring(name.lastIndexOf("_"))
      val nameNoSuffix = name.stripSuffix(suffix)
      globalToParam.getOrElse(nameNoSuffix, nameNoSuffix) + suffix
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
          case None => assert(false, f"Missing predicate argument ${p}")
        }
      }

      val predVarShifts = funcContext.postPred.argVars
        .zipWithIndex
        .map({ case (v, i) => ctxArgNameToIndex(lookup(v.name))-i })
        .toList

      predVarShifts.foreach(i => printlnDebug(f"diff: ${i}"))

      VariablePermVisitor(pre, IVarShift(predVarShifts, 0))
    }

    //prePredArgIndexToName.map

    MergableContract(funcContext, mapPrePredVars(), mapPostPredVars())
  }

  private def usePreStateVars(f: IFormula): IFormula = {
    /*
      Problems:
      1. The new function context has a larger set of global
         variables and function arguments than any of the two
         function contexts have on their own.
      2. There may be an overlap between variable indices in the
         formulas, i.e. one index means one thing in one formula
         and another thing in the other
      3. Predicate variable indicies used in the pre-state formula
         must be translated to mean the pre-state value of the variable
         when the formula is used in post-state context.
    */
    f
  }

  /**
   * Assumes that this contract and "other" refer to the same function.
   * The [[FunctionContext]] from this instance will be used as
   * the context for the new contract.
   * 
   * @param other The contract to meet with
   */
  def meet(other: MergableContract): MergableContract = {
  /*
    pre1ToCommonPreIndex
    pre2ToCommonPreIndex

    postPred1ToCommonPostIndex
    postPred2ToCommonPostIndex

    toOld = prePredToPostPredOldIndex

    comPre1 = pre1ToCommonPreIndex(prePred1)
    comPre2 = pre2ToCommonPreIndex(prePred2)
    comPost1 = post1ToCommonPostIndex(postPred1)
    comPost2 = post2ToCommonPostIndex(postPred2)
    newPrePred = comPre1 \/ comPre2
    newPostPred = (toOld(comPre1) ==> comPost1) /\ (toOld(comPre2) ==> comPost2)
  */

    def pre1ToCommonPreIndex(form: IFormula) = {
      val commonIndex = new MHashMap[CCVar, Int]
      
      funcContext.prePred.argVars.zipWithIndex.foreach(pair => commonIndex += pair)

    }

    val newPrePredFormula = pre ||| other.pre
    val newPostPredFormula = 
      (usePreStateVars(pre) ===> post) &&&
      (usePreStateVars(other.pre) ===> other.post)
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

//  private val funcGroups = groupFunctionsByOriginalName()

//  private val contracts = callSiteTransforms.map(t => t.)

//  private def groupFunctionsByOriginalName() = {
//    callSiteTransforms
//      .map(transform => 
//        transform.getAstAdditions().transformedFunctionDeclarations
//          .keySet.map(name => (transform.originalFuncName, name)))
//      .flatten
//      .distinct
//      .groupBy(origTransPair => origTransPair._1)
//      .mapValues(pairs => pairs.map({case (orig ,trans) => trans}))
//  }

  def apply(): (Solution, Map[String,CCReader.FunctionContext]) = {
    // 1. group predicates in solution by their original function name.
    // 2. map variable indicies in pre/postcondition formulas back
    //    to the original function pre/postcondition formula indicies
    // 3. reduce the corresponding formulas by "meet". Keep the predicate
    //    corresponding to the original function but associate it with
    //    the reduced formula in the new solution.
    // 4. use function context of original function.

    def isAssociatedWithTransformedFunction(pred: Predicate) = {
      functionContexts.exists({ case (funcName, ctx) => ctx.prePred.pred == pred || ctx.postPred.pred == pred })
    }

//    def findContext(funcName: String) = {
//      functionContexts(funcName)
//    }
//
//    def usePreStateVars(f: IFormula): IFormula = {
//      f
//    }
//
//    def meetByPair(contract1: (IFormula, IFormula), contract2: (IFormula, IFormula)):(IFormula, IFormula) = {
//      val newPrePredFormula = contract1._1 ||| contract2._1
//      val newPostPredFormula = 
//        (usePreStateVars(contract1._1) ===> contract1._2) &&&
//        (usePreStateVars(contract2._1) ===> contract2._2)
//      (newPrePredFormula, newPostPredFormula)
//    }

    def toContract(context: CCReader.FunctionContext, solution: SolutionProcessor.Solution) = {
      MergableContract(context, solution(context.prePred.pred), solution(context.postPred.pred))
    }

    val additions = callSiteTransforms.map(t => t.getAstAdditions()).reduce((a,b) => {a += b})

//    for ((key, value) <- additions.globalVariableIdToParameterId) {
//        printlnDebug(f"key: ${key} -> value: ${value}")
//    }

    val contractsByOriginalFuncId = additions.transformedFunctionIdToOriginalId
      .groupBy({case (transformedId, origId) => origId })
      .mapValues(_.keySet.map(funcId => toContract(functionContexts(funcId), solution)))

    var merged = solution.filter({case (pred, formula) => !isAssociatedWithTransformedFunction(pred)})

    for ((originalId, contracts) <- contractsByOriginalFuncId) {
      val fullContract = 
        contracts.fold(toContract(functionContexts(originalId), solution))(
            (original, transformed) => 
                original.meet(transformed.mapTo(original.funcContext, additions.globalVariableIdToParameterId)))

      merged = 
        merged + 
        (fullContract.funcContext.prePred.pred -> fullContract.pre) +
        (fullContract.funcContext.postPred.pred -> fullContract.post)
    }
    (merged, functionContexts.filterKeys(funcId => contractsByOriginalFuncId.contains(funcId)))
  }
}
