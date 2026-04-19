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

package tricera.concurrency.ccreader

import ap.parser._
import ap.parser.IExpression.ConstantTerm
import ap.types.SortedConstantTerm
import hornconcurrency.ParametricEncoder
import lazabs.horn.bottomup.HornClauses
import tricera.{Literals, properties}
import tricera.Util.{SourceInfo, getSourceInfo}
import tricera.acsl.{ACSLTranslator, FunctionContract}
import tricera.concurrency.ccreader.CCExceptions.TranslationException
import tricera.concurrency.concurrent_c.Absyn._
import tricera.parsers.AnnotationParser
import tricera.parsers.AnnotationParser._

import scala.jdk.CollectionConverters._

object StatementContracts {

  private var counter = 0
  def freshName(prefix : String) : String = {
    counter += 1
    prefix + (counter - 1)
  }

  // strip `/*@ ... */` or `//@ ...` from an annotation
  private def annotationString(annot : Annotation) : String = {
    val str = annot match {
      case a : Annot1 => a.annotationstring_
    }
    str.substring(2, str.length - 2)
  }

  def isStatementContract(annotStm : Annotation) : Boolean =
    AnnotationParser(annotationString(annotStm)) match {
      case scala.Seq(ContractGen) => true
      case scala.Seq(MaybeACSLAnnotation(annot, _)) =>
        try ACSLTranslator.parseAnnotationAst("/*@" + annot + "*/")
              .isInstanceOf[tricera.acsl.Absyn.AnnotContract]
        catch { case _ : Throwable => false }
      case _ => false
    }

  def translate(tctx         : TranslationContext,
                fctx         : ContractBodyContext,
                bodyTrans    : (Stm, CCPredicate, CCPredicate) => Unit,
                functionName : String,
                returnPred   : Option[CCPredicate],
                annotStm     : Annotation,
                bodyStm      : Stm,
                entry        : CCPredicate,
                exit         : CCPredicate) : Unit = {
    import HornClauses._
    import tctx._

    bodyStm match {
      case _ : DecS => throw new TranslationException(
        "A statement contract's body must not be a bare declaration; " +
        "wrap it in a compound statement.")
      case _ =>
    }

    val annotationInfo =
      AnnotationParser(annotationString(annotStm))
    val isContractGen = annotationInfo == scala.Seq(ContractGen)
    val annotationText : Option[String] = annotationInfo match {
      case scala.Seq(ContractGen)               => None
      case scala.Seq(MaybeACSLAnnotation(a, _)) => Some("/*@" + a + "*/")
      case _ => throw new TranslationException(
        "Expected a statement contract annotation.")
    }

    val annotSrc    = Some(getSourceInfo(annotStm))
    val bodySrc     = Some(getSourceInfo(bodyStm))
    val contractNm  = freshName(Literals.stmtContractPrefix)

    val outerVars   = scope.allFormalVars.toList
    val outerTerms  = outerVars.map(v => IConstant(v.term))
    val heapVarSet  =
      if (modelHeap) heapVars.values.toSet else Set.empty[CCVar]
    val nonHeapOuter = outerVars.filterNot(heapVarSet.contains)
    val heapOuter    = outerVars.filter(heapVarSet.contains)

    scope.LocalVars.pushFrame
    val oldVars = nonHeapOuter.map(v =>
      new CCVar(v.name + Literals.preExecSuffix,
                v.srcInfo, v.typ, ContractOldStorage(contractNm, v.name)))
    val oldHeapVars = heapOuter.map(v =>
      new CCVar(v.name + Literals.preExecSuffix,
                v.srcInfo, v.typ, ContractOldStorage(contractNm, v.name)))
    val outerToOld : Map[CCVar, CCVar] =
      ((nonHeapOuter zip oldVars) ++ (heapOuter zip oldHeapVars)).toMap
    val outerOld      = outerVars.map(outerToOld)
    val outerOldTerms = outerOld.map(v => IConstant(v.term))
    for (v <- outerOld) scope.LocalVars.addVar(v)

    val encHasContract       = functionPostOldArgs.contains(functionName)
    val nestedInsideContract = fctx.contractBodyReturn.isDefined
    val canForwardReturn =
      returnPred.isDefined && !encHasContract && !nestedInsideContract

    val encReturn : Option[EnclosingReturn] =
      if (canForwardReturn)
        EnclosingReturn.fromOptional(returnPred, outerVars)
      else None

    val oldLookup : Map[String, CCVar] =
      (nonHeapOuter ++ heapOuter).map(_.name)
        .zip(oldVars ++ oldHeapVars).toMap
    val postLookup : Map[String, CCVar] =
      (nonHeapOuter ++ heapOuter).map(v => v.name -> v).toMap
    val ctx = new RegionAnnotationContext(
      tctx       = tctx,
      oldLookup  = oldLookup,
      postLookup = postLookup,
      params     = Nil,
      globals    = nonHeapOuter,
      // \result in a returns clause refers to enclosing function's return
      result     = encReturn.flatMap(_.result.headOption),
      srcInfo    = getSourceInfo(annotStm))
    val contract : Option[FunctionContract] = annotationText match {
      case Some(text) =>
        try Some(ACSLTranslator.translateACSL(text, ctx)
                 .asInstanceOf[FunctionContract])
        catch {
          case e : Throwable =>
            scope.LocalVars.popFrame()
            throw e
        }
      case None => None
    }

    val returnResultSlot : scala.Seq[CCVar] =
      encReturn.map(_.result).getOrElse(Nil)
    val returnPredFormalCount =
      encReturn.map(_.formals.size).getOrElse(0)

    val prePred  = newPred(contractNm + Literals.predPreSuffix,
                           outerOld, annotSrc)
    val postPred = newPred(contractNm + Literals.predPostSuffix,
                           outerOld ++ outerVars, annotSrc)

    val returnContractNm = contractNm + "_ret"
    val returnsContract : Option[FunctionContract] =
      contract.map(c => new FunctionContract(
        c.pre, c.returns.getOrElse(IBoolLit(true)),
        c.assignsAssert, c.assignsAssume,
        c.srcInfo, c.postSrcInfo))
    val (returnBodyPred, returnRegistration) :
        (Option[CCPredicate], Option[ContractRegistration]) =
      if (canForwardReturn) {
        val bodyPred = newPred(contractNm + "_return",
                               outerVars ++ outerOld ++ returnResultSlot,
                               annotSrc)
        val postRet  = newPred(returnContractNm + Literals.predPostSuffix,
                               outerOld ++ outerVars ++ returnResultSlot,
                               annotSrc)
        val retReg = ContractRegistration(
          name            = returnContractNm,
          kind            = ContractKind.Statement,
          prePred         = prePred,
          postPred        = postRet,
          contract        = returnsContract,
          isUserAnnotated = !isContractGen,
          returnVariant   = None,
          srcInfo         = Some(getSourceInfo(annotStm)))
        (Some(bodyPred), Some(retReg))
      } else (None, None)

    registerStatementContract(
      name            = contractNm,
      prePred         = prePred,
      postPred        = postPred,
      contract        = contract,
      isUserAnnotated = !isContractGen,
      returnVariant   = returnRegistration,
      srcInfo         = Some(getSourceInfo(annotStm)))

    val returnPostPred : Option[CCPredicate] =
      returnRegistration.map(_.postPred)

    val bodyEntry = newPred(Nil, annotSrc)
    val bodyExit  = newPred(Nil, bodySrc)

    val savedClauses    = clauses.toList
    val savedAssertions = assertionClauses.toList
    clauses.clear()
    assertionClauses.clear()

    var bodyCanReturn = false

    try {
      // bodyEntry(outer, outerOld) :- prePred(outer)
      output(addRichClause(Clause(
        atom(bodyEntry, outerTerms ++ outerTerms),
        List(atom(prePred, outerTerms)),
        true), annotSrc))

      val labelsBeforeBody     = fctx.labelledLocs.keySet.toSet
      val jumpCountBeforeBody  = fctx.jumpLocs.size
      val clauseCountBeforeBody = clauses.size
      fctx.withinContractedBody(returnBodyPred) {
        bodyTrans(bodyStm, bodyEntry, bodyExit)
      }
      // check if translation added a return pred into the CHCs
      bodyCanReturn = returnBodyPred.exists(p =>
        clauses.iterator.drop(clauseCountBeforeBody)
          .exists { case (c, _) => c != null && c.head.pred == p.pred })

      if (contract.exists(_.returns.isEmpty) && bodyCanReturn)
        throw new TranslationException(
          "A statement contract's body contains a `return`; " +
          "the contract must include a `returns:` clause.")

      val bodyInternalLabels =
        fctx.labelledLocs.keySet.toSet.diff(labelsBeforeBody)
      val bodyJumps =
        fctx.jumpLocs.iterator.drop(jumpCountBeforeBody).toList
      for ((label, _, _, _, jumpSrc) <- bodyJumps
           if !bodyInternalLabels(label))
        throw new TranslationException(
          s"""goto "$label" (${jumpSrc.line}:${jumpSrc.col}) leaves the """ +
          "statement contract body, which is not yet supported.")

      // resolve body-internal gotos locally
      for ((label, jumpPred, jumpVars, position, jumpSrc) <- bodyJumps) {
        val (targetPred, targetVars) = fctx.labelledLocs(label)
        val commonVars = (jumpVars zip targetVars).takeWhile {
          case (a, b) => a == b
        }.map(_._1)
        val jumpArgs = commonVars ++ (
          for (i <- 0 until (jumpPred.arity - commonVars.size))
          yield IConstant(new ConstantTerm("preArg_" + i)))
        val targetArgs = commonVars ++ (
          for (i <- 0 until (targetPred.arity - commonVars.size))
          yield IConstant(new ConstantTerm("postArg_" + i)))
        val bridge = Clause(atom(targetPred, targetArgs),
                            List(atom(jumpPred, jumpArgs)),
                            true)
        addRichClause(bridge, Some(jumpSrc))
        clauses(position) = (bridge, ParametricEncoder.NoSync)
        fctx.usedJumpTargets.put(targetPred, label)
      }
      fctx.jumpLocs.trimEnd(fctx.jumpLocs.size - jumpCountBeforeBody)

      // `false :- bodyExit, !(post && assigns)`.
      //  postPred(outerOld, outer) :- bodyExit(outer, outerOld)
      output(addRichClause(Clause(
        atom(postPred, outerOldTerms ++ outerTerms),
        List(atom(bodyExit, outerTerms ++ outerOldTerms)),
        true), bodySrc))

      (returnBodyPred, returnPostPred) match {
        case (Some(bodyPred), Some(postRet)) =>
          val retTerms = returnResultSlot.map(v => IConstant(v.term))
          output(addRichClause(Clause(
            atom(postRet, outerOldTerms ++ outerTerms ++ retTerms),
            List(atom(bodyPred, outerTerms ++ outerOldTerms ++ retTerms)),
            true), annotSrc))
        case _ =>
      }

      functionClauses.put(contractNm,
        functionClauses.getOrElse(contractNm, Nil) ++ clauses.toList)
      functionAssertionClauses.put(contractNm,
        functionAssertionClauses.getOrElse(contractNm, Nil) ++
          assertionClauses.toList)
    } finally {
      clauses.clear()
      assertionClauses.clear()
      clauses ++= savedClauses
      assertionClauses ++= savedAssertions
      scope.LocalVars.popFrame
    }

    // `pre :- entry`.
    val entryAtom = atom(entry, scope.allFormalVarTerms take entry.arity)
    assertionClauses += mkRichAssertionClause(
      Clause(atom(prePred, outerTerms), List(entryAtom), true),
      annotSrc,
      properties.FunctionPrecondition(contractNm, annotSrc))

    val postTerms : scala.Seq[ITerm] = outerVars.map { v =>
      if (v.storage.isInstanceOf[ContractOldStorage]) IConstant(v.term)
      else IConstant(new SortedConstantTerm(
        v.name + Literals.postExecSuffix, v.typ.toSort))
    }

    output(addRichClause(Clause(
      atom(exit, postTerms),
      List(entryAtom, atom(postPred, outerTerms ++ postTerms)),
      true), annotSrc))

    if (bodyCanReturn) (returnBodyPred, returnPostPred) match {
      case (Some(_), Some(postRet)) =>
        val retResultTerms : scala.Seq[ITerm] =
          returnResultSlot.map(v => IConstant(new SortedConstantTerm(
            "_res", v.typ.toSort)))
        val rpArgs = postTerms.take(returnPredFormalCount) ++ retResultTerms
        output(addRichClause(Clause(
          atom(returnPred.get, rpArgs),
          List(entryAtom,
               atom(postRet, outerTerms ++ postTerms ++ retResultTerms)),
          true), annotSrc))
      case _ =>
    }
  }
}
