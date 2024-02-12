/**
 * Copyright (c) 2021-2022 Pontus Ernstedt
 *               2022-2023 Zafer Esen. All rights reserved.
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

package tricera.acsl

import tricera.acsl.{Absyn => AST}

import collection.JavaConverters._
import ap.parser._
import ap.theories.nia.GroebnerMultiplication._
import ap.types.{Sort, SortedConstantTerm}
import ap.theories.Heap
import tricera.Util.{SourceInfo, getSourceInfo}
import tricera.concurrency.ccreader._
import CCExceptions._

class ACSLException(msg : String) extends Exception(msg)
class ACSLParseException(msg : String, srcInfo : SourceInfo) extends Exception(msg)

object ACSLTranslator {

  trait AnnotationContext {
    def getGlobals : Seq[CCVar]
    def sortWrapper(s: Sort): Option[IFunction]
    def sortGetter(s: Sort): Option[IFunction]
    def getCtor(s: Sort): Int
    def getTypOfPointer(t: CCType): CCType
    def isHeapEnabled: Boolean
    def getHeap: Heap
    def getHeapTerm: ITerm
    def getOldHeapTerm : ITerm
    val annotationBeginSourceInfo : SourceInfo
    val annotationNumLines : Int
  }

  trait FunctionContext extends AnnotationContext {
    def getOldVar(ident : String) : Option[CCVar]
    def getPostGlobalVar(ident : String) : Option[CCVar]
    def getParams  : Seq[CCVar]
    def getResultVar : Option[CCVar]
  }

  trait StatementAnnotationContext extends AnnotationContext {
    def getTermInScope (name : String) : Option[CCTerm]
  }

  private[acsl] def getActualLine(ctx : AnnotationContext, line : Int) = {
    ctx.annotationBeginSourceInfo.line + line
  }
  private[acsl] def getActualSourceInfo (ctx : AnnotationContext,
                                   srcInfo : SourceInfo) : SourceInfo = {
    val begin = ctx.annotationBeginSourceInfo
    SourceInfo(line   = begin.line + srcInfo.line,
               col    = srcInfo.col)
  }

  @throws[ACSLException]("if not called with the right context")
  @throws[ACSLParseException]("if parsing or translation fails")
  def translateACSL(annot : String,
                    ctx   : AnnotationContext) : ParsedAnnotation = {
    val l : Yylex = new Yylex(new java.io.StringReader(preprocess(annot)))
    val p : parser = new parser(l, l.getSymbolFactory())
    val ast : AST.Annotation = p.pAnnotation()
    val translator = new ACSLTranslator(ctx)

    ast match {
      case ac : AST.AnnotContract =>
        ctx match {
          case funCtx : FunctionContext =>
            translator.translate(ac.functioncontract_)
          case _ => throw new ACSLException("A function context is " +
                                            "needed to parse a function contract.")
        }
      case ac : AST.AnnotAssertion =>
        ctx match {
          case stmCtx : StatementAnnotationContext =>
            translator.translate(ac.assertion_, stmCtx)
          case _ => throw new ACSLException("A statement context is " +
                                            "needed to parse a statement annotation.")
        }
      case ac : AST.LoopAnnot =>
        ctx match {
          case stmCtx : StatementAnnotationContext =>
            translator.translate(ac.loopinvariant_, stmCtx)
          case _ => throw new ACSLException("A statement context is " +
                                            "needed to parse a loop invariant annotation.")
        }
      case _ => throw new ACSLException("Not a contract or " +
                                        "statement annotation.")
    }
  }

  private def preprocess(annot : String) : String = {
    def replaceAtSymbols(annot : String) : String = {
      val (left, right) = annot.splitAt(3)
      left.concat(right.replace('@', ' '))
    }
    replaceAtSymbols(annot)
  }

}

/**
 * @param ctx Context providing information about the parsed program where
 *            the ACSL annotation appears in.
 */
class ACSLTranslator(ctx : ACSLTranslator.AnnotationContext) {
  import scala.collection.mutable.{HashMap => MHashMap}
  import ACSLTranslator._

  private val printer = new tricera.acsl.PrettyPrinterNonStatic

  val locals = new MHashMap[String, CCTerm]
  var vars: Map[String, CCVar] = Map()
  var inPostCond = false
  var useOldHeap = false
  // TODO: Make all `translate` private?

  // ---- Statement annotations (e.g., assertions) -----------
  def translate(assertAnnotation : AST.Assertion,
                stmCtx           : StatementAnnotationContext)
  : StatementAnnotation = {
    val srcInfo = getSourceInfo(assertAnnotation)
    assertAnnotation match {
      case regularAssertion : AST.RegularAssertion =>
            val f = translate(regularAssertion.expr_)
            StatementAnnotation(f.toFormula, isAssert = true)
      case _ =>
        throw new ACSLParseException("Behaviour assertions are " +
          "currently unsupported.", srcInfo)
    }
  }

  // ---- Loop annotations -----------------------------------
  def translate(loopInvariantAnnotation : AST.LoopInvariant,
                stmCtx                  : StatementAnnotationContext)
  : LoopAnnotation = {
    loopInvariantAnnotation match {
      case inv : AST.LoopInvSimple =>
        val f = translate(inv.expr_)
        LoopAnnotation(f.toFormula)
    }
  }

  // ---- Contracts ------------------------------------------
  def translate(contract : AST.FunctionContract) : FunctionContract = contract match {
    case c : AST.Contract =>
      val rcs = c.listrequiresclause_.asScala.toList
      val scs = c.listsimpleclause_.asScala.toList

      val nils : (List[AST.SimpleClauseEnsures], List[AST.SimpleClauseAssigns])
        = (Nil, Nil)
      val (ecs, acs) =
        scs.foldRight(nils) {
          case (ec : AST.SimpleClauseEnsures, (ecs, acs)) => (ec :: ecs, acs)
          case (ac : AST.SimpleClauseAssigns, (ecs, acs)) => (ecs, ac :: acs)
          case _ => throw new ACSLParseException("Unsupported simple clause.",
                                                 getSourceInfo(c))
        }

      // TODO: do not use "and" and "toFormula" below,losing source information!
      // NOTE: `pre` and `post` defaults to true given usage of `and`.
      useOldHeap = true
      val pre  : IFormula = IExpression.and(rcs.map(f => translate(f).toFormula))
      useOldHeap = false
      val post : IFormula = IExpression.and(ecs.map(f => translate(f).toFormula))

      // FIXME: Refactor and break out in functions!
      val assigns : (IFormula, IFormula) = acs match {
        case Nil => (IBoolLit(true), IBoolLit(true))
        case acs =>
          val (idents, ptrDerefs) : (Set[CCExpr], Set[CCExpr]) =
            acs.foldLeft(Set[CCExpr](), Set[CCExpr]()) ({(sets, clause) =>
              val (i, p) =
                translateAssigns(clause.assignsclause_
                  .asInstanceOf[AST.AnAssignsClause])
              (i.union(sets._1), p.union(sets._2))
            })

          val funCtx = ctx.asInstanceOf[FunctionContext]

          val globConstraint : IFormula =
            if (idents.isEmpty) {
              ctx.getGlobals.foldLeft(IBoolLit(true) : IFormula) (
                (formula, globVar) => {
                  val glob    : ITerm = funCtx.getPostGlobalVar(globVar.name).get.term//globVar.term
                  val globOld : ITerm = funCtx.getOldVar(globVar.name).get.term
                  formula &&& glob === globOld
                }
              )
            } else {
              val globals : Seq[ITerm] = ctx.getGlobals.map(_.term)
              val oldGlobals : Seq[ITerm] =
                ctx.getGlobals.map(g => funCtx.getOldVar(g.name).get.term)
              val globToOld : Map[ITerm, ITerm] =
                globals.zip(oldGlobals).toMap

              val nonAssignedGlobals : Set[ITerm] =
                globals.toSet.diff(idents.map(_.toTerm))

              nonAssignedGlobals.foldLeft(IBoolLit(true) : IFormula) (
                (formula, term) => formula &&& term === globToOld(term)
              )
            }

          val (heapAssert, heapAssume) : (IFormula, IFormula) =
            if (ptrDerefs.isEmpty) {
                if (funCtx.isHeapEnabled) {
                  val sameHeap = funCtx.getHeapTerm === funCtx.getOldHeapTerm
                  (sameHeap, sameHeap)
                } else {
                  (IBoolLit(true), IBoolLit(true))
                }
            } else {
                val ptrs = ptrDerefs.map(_.toTerm)

                import ap.parser.IExpression.toFunApplier
                val heap : Heap = funCtx.getHeap
                val newHeap : ITerm = funCtx.getHeapTerm
                val oldHeap : ITerm = funCtx.getOldHeapTerm

                // Implicit existensional
                val addrObjPairs : List[(ITerm, ITerm)] =
                  (for ((ptr, i) <- ptrs zipWithIndex) yield {
                    val o = new SortedConstantTerm("_o" + i, heap.ObjectSort)
                    (ptr, IConstant(o))
                  }).toList

                val modifiedHeap : ITerm =
                  addrObjPairs.foldLeft(oldHeap) ({
                    case (h, pair) => heap.write(h, pair._1, pair._2)
                  })

                val ptrObjPairs : List[(CCExpr, ITerm)] =
                  ptrDerefs.zip(addrObjPairs.map(_._2)).toList

                val corrSort : IFormula =
                  ptrObjPairs.foldLeft(IBoolLit(true) : IFormula) (
                    (formula, pair) => {
                      val (p, obj) = pair
                      val sort : Sort =
                        p.typ.asInstanceOf[CCHeapPointer].typ.toSort
                      val corr : IFormula =
                        funCtx.getHeap.heapADTs.hasCtor(obj, ctx.getCtor(sort))
                      formula &&& corr
                    }
                  )

                val assumeConstr : IFormula
                  = newHeap === modifiedHeap &&& corrSort

                // Implicit universal
                val quant : ITerm =
                  new SortedConstantTerm("_p", funCtx.getHeap.AddressSort)
                val quantifiedNotEqual : IFormula =
                  ptrs.foldLeft(IBoolLit(true) : IFormula) (
                    (formula, ptr) => formula &&& quant =/= ptr
                  )

                val readEq : IFormula =
                  heap.read(newHeap, quant) === heap.read(oldHeap, quant)
                val assertConstr : IFormula = quantifiedNotEqual ==> readEq

                (assertConstr, assumeConstr)
            }
          (heapAssert &&& globConstraint, heapAssume &&& globConstraint)
      }

      val postSrcInfo = ecs match {
        case Nil => getSourceInfo(c) // no post-conditions, value does not matter
        case hd :: tl => getSourceInfo(hd)
      }

      // todo: have separate line numbers for ecs
      new FunctionContract(pre, post, assigns._1, assigns._2,
                           getSourceInfo(c),
                           getActualSourceInfo(ctx, postSrcInfo))

    case _ => throwNotImpl(contract)
  }

  // FIXME: Return ITerm directly?
  def translateAssigns(clause : AST.AnAssignsClause) : (Set[CCExpr], Set[CCExpr]) = {
    val srcInfo = getSourceInfo(clause)
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, v))).toMap
    clause.locations_ match {
      case ls : AST.LocationsSome    =>
        val tSets : List[AST.TSet] =
          ls.listlocation_.asScala.toList
          .map(_.asInstanceOf[AST.ALocation].tset_)
        val nils = (Nil : List[CCExpr], Nil : List[CCExpr])
        val terms : (List[CCExpr], List[CCExpr]) = tSets.foldRight(nils) ({
          case (t : AST.TSetTerm, (idents, ptrDerefs)) =>
            t.expr_ match {
              case i : AST.EIdent => (translate(i) :: idents, ptrDerefs)
              case p : AST.EUnary
                if p.unaryop_.isInstanceOf[AST.UnaryPtrDeref] => {
                useOldHeap = true
                val res = (idents, translateTerm(p.expr_) :: ptrDerefs)
                useOldHeap = false
                res
              }
            case _ => throw new ACSLParseException("Only global identifiers or "
              + "heap pointer dereferences allowed in assigns-clauses.", srcInfo)
          }
          case t => throwNotImpl(t)
        })
        (terms._1.toSet, terms._2.toSet)
      case _  : AST.LocationsNothing => (Set(), Set())
    }
  }


  // FIXME: Type is specified already.

  /**
   * Translates assigns / ensures clauses.
   */
  def translate(clause : AST.SimpleClause) : CCFormula = clause match {
    case ac : AST.SimpleClauseAssigns => throwNotImpl(ac)
    case ec : AST.SimpleClauseEnsures => translate(ec.ensuresclause_)
  }

  def translate(clause : AST.EnsuresClause) : CCFormula = {
    val funCtx = ctx.asInstanceOf[FunctionContext]
    inPostCond = true
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, v))).toMap
    val res = translatePred(clause.asInstanceOf[AST.AnEnsuresClause].expr_)
    inPostCond = false
    res
  }

  def translate(clause : AST.RequiresClause) : CCFormula = {
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams ++ ctx.getGlobals).map(v =>
      (v.name, funCtx.getOldVar(v.name).get)).toMap
    translatePred(clause.asInstanceOf[AST.ARequiresClause].expr_)
  }

  def translate(expr : AST.Expr) : CCExpr = expr match {
    case e : AST.ENaming1  => ???
    case e : AST.ENaming2  => ???
    case _ :   AST.EForAll
         | _ : AST.EExists => translateQuantified(expr)
    case e : AST.EBinding  => ???
    case e : AST.ETernary  => translateTernary(e)
    case _ :   AST.EEquiv
         | _ : AST.EImplies
         | _ : AST.EOr
         | _ : AST.EXOr
         | _ : AST.EAnd      => translateBinaryLogicOp(expr)
    case e : AST.EBitEquiv   => ???
    case e : AST.EBitImplies => ???
    case e : AST.EBitOr      => ???
    case e : AST.EBitXOr     => ???
    case e : AST.EBitAnd     => ???
    case e : AST.EEq         => translateEqNeq(e)
    case e : AST.ENeq        => translateEqNeq(e)
    case e : AST.ERelOp      => translateRelOp(e)
    case e : AST.ELeftShift  => ???
    case e : AST.ERightShift => ???
    case _ :   AST.EPlus
         | _ : AST.EMinus
         | _ : AST.EMult
         | _ : AST.EDiv
         | _ : AST.EMod       => translateArith(expr)
    case e : AST.EUnary       => translateUnary(e)
    case e : AST.ETypeCast    => ???
    case e : AST.ESizeOfTerm  => ???
    case e : AST.ESizeOfType  => ???
    case e : AST.EArrayAccess => translateArrayAccessExpr(e)
    case e : AST.EStructFieldAccess =>
      translateStructFieldAccessExpr(e)
    case e : AST.EStructPtrFieldAccess => ???
    case e : AST.EArrayFunMod => ???
    case e : AST.EFieldFunMod => ???
    case e : AST.EApplication => ???
    case e : AST.EOld         => translateOldExpr(e)
    case e : AST.EValid       => translateValidExpr(e)
    case e : AST.ELit         => translateLitExpr(e.lit_)
    case e : AST.EIdent       => translateIdentExpr(e)
    case e : AST.EResult      => translateResultExpr(e)
  }

  def translateLitExpr(lit : AST.Lit) : CCExpr = {
    import IExpression._
    import ap.basetypes.IdealInt
    val srcInfo = Some(getSourceInfo(lit))
    lit match {
      case t : AST.LitTrue  =>CCFormula(IBoolLit(true), CCBool, srcInfo)
      case t : AST.LitFalse => CCFormula(IBoolLit(false), CCBool, srcInfo)
      case t : AST.LitInt =>
        CCTerm(i(IdealInt(t.unboundedinteger_)), CCInt, srcInfo)
      case t : AST.LitReal => ???
      case t : AST.LitString => ???
      case t : AST.LitChar => ???
    }
  }

  /**
   * term x term -> predicate
   * In the ACSL grammar the return type of rel ops is ambiguous: it can be
   * a term or a predicate. Here we disambiguate by picking the latter.
   * TODO: support chained applications
   */
  def translateRelOp(relOp : AST.ERelOp) : CCFormula = {
    val lhs : ITerm = translate(relOp.expr_1).toTerm
    val rhs : ITerm = translate(relOp.expr_2).toTerm
    val srcInfo = Some(getSourceInfo(relOp))
    CCFormula(relOp.relop_ match {
      case _ : AST.RelOpLEQ => lhs <= rhs
      case _ : AST.RelOpGEQ => lhs >= rhs
      case _ : AST.RelOpGT  => lhs > rhs
      case _ : AST.RelOpLT  => lhs < rhs
    }, CCBool, srcInfo)
  }

  /**
   * term x term -> predicate
   * In the ACSL grammar the return type of rel ops is ambiguous: it can be
   * a term or a predicate. Here we disambiguate by picking the latter.
   * TODO: support chained applications
   */
  def translateEqNeq(expr : AST.Expr) : CCFormula = {
    val srcInfo = getSourceInfo(expr)
    CCFormula(
      expr match {
        case eq  : AST.EEq =>
          val lhs : ITerm = translateTerm(eq.expr_1).toTerm
          val rhs : ITerm = translateTerm(eq.expr_2).toTerm
          lhs === rhs
        case neq : AST.ENeq =>
          val lhs : ITerm = translateTerm(neq.expr_1).toTerm
          val rhs : ITerm = translateTerm(neq.expr_2).toTerm
          lhs =/= rhs
        case _ =>
          throw new ACSLParseException(s"Op must be '==' or '!=', got " +
                                       s"${printer print expr}.", srcInfo)
      }, CCBool, Some(srcInfo))
  }

  def translateArith(expr : AST.Expr) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    CCTerm(
      expr match {
        case eq : AST.EPlus   =>
          val lhs : ITerm = translateTerm(eq.expr_1).toTerm
          val rhs : ITerm = translateTerm(eq.expr_2).toTerm
          lhs + rhs
        case neq : AST.EMinus =>
          val lhs : ITerm = translateTerm(neq.expr_1).toTerm
          val rhs : ITerm = translateTerm(neq.expr_2).toTerm
          lhs - rhs
        case neq : AST.EMult =>
          val lhs : ITerm = translateTerm(neq.expr_1).toTerm
          val rhs : ITerm = translateTerm(neq.expr_2).toTerm
          lhs * rhs
        case neq : AST.EDiv  =>
          val lhs : ITerm = translateTerm(neq.expr_1).toTerm
          val rhs : ITerm = translateTerm(neq.expr_2).toTerm
          lhs / rhs
        case neq : AST.EMod   =>
          val lhs : ITerm = translateTerm(neq.expr_1).toTerm
          val rhs : ITerm = translateTerm(neq.expr_2).toTerm
          lhs % rhs
        case _              =>
          throw new ACSLParseException(
            "Op is recognized, got " + (printer print expr), srcInfo)
      }, CCBool, Some(srcInfo))
  }

  /**
   * Helper function to translate expressions into predicates.
   * Throws an error if the expression is not an actual predicate.
   */
  def translatePred(expr : AST.Expr) : CCFormula = {
    val srcInfo = getSourceInfo(expr)
    val t = translate(expr)
    t match {
      case pred : CCFormula => pred
      case _ =>
        throw new ACSLParseException(
          "Expected a predicate, but got " + (printer print expr), srcInfo)
    }
  }

  /**
   * Helper function to translate expressions into terms.
   * Throws an error if the expression is not an actual term.
   */
  def translateTerm(expr : AST.Expr) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    val t = translate(expr)
    t match {
      case term : CCTerm => term
      case _                =>
        throw new ACSLParseException(
          "Expected a term, but got " + (printer print expr), srcInfo)
    }
  }

  /**
   * Translate logical operators that are only applicable to predicates.
   * I.e.,: "&&" | "||" | "==>" | "<==>" | "^^"
   */
  def translateBinaryLogicOp(expr : AST.Expr) : CCFormula = {
    val srcInfo = Some(getSourceInfo(expr))
    expr match {
      case e : AST.EEquiv => // <==>
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCFormula(lhs.toFormula <=> rhs.toFormula, CCBool, srcInfo)
      case e : AST.EImplies => // ==>
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCFormula(lhs.toFormula ==> rhs.toFormula, CCBool, srcInfo)
      case e : AST.EOr => // ||
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCFormula(lhs.toFormula ||| rhs.toFormula, CCBool, srcInfo)
      case e : AST.EXOr => // ^^
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCFormula(lhs.toFormula </> rhs.toFormula, CCBool, srcInfo)
      case e : AST.EAnd => // &&
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCFormula(lhs.toFormula &&& rhs.toFormula, CCBool, srcInfo)
      case _ =>
        throw new ACSLParseException(
          "Not a logical operator: " + (printer print expr), srcInfo.get)
    }
  }

  /**
   * There are three cases in the ACSL grammar:
   *   term ? term : term -> term
   *   term ? pred : pred -> pred
   *   pred ? pred : pred -> pred
   */
  def translateTernary(expr : AST.ETernary) : CCExpr = {
    val cond : CCExpr = translate(expr.expr_1)
    val left : CCExpr = translate(expr.expr_2)
    val right : CCExpr = translate(expr.expr_3)
    val srcInfo = Some(getSourceInfo(expr))

    (cond, left, right) match {
      case (c@CCTerm(_, _, _), l@CCTerm(_,lType,_), r@CCTerm(_,rType,_)) =>
        if (lType != rType) {
          // TODO: support implicit type casts.
          throw new ACSLParseException(
            s"Type mismatch in $expr: $lType vs $rType. (Implicit casts are " +
            s"currently unsupported.)", srcInfo.get)
        }
        CCTerm(ITermITE(cond.toFormula, left.toTerm, right.toTerm),
               lType, srcInfo)
      case (c@CCTerm(_, _, _), l@CCFormula(_,_,_), r@CCFormula(_,_,_)) =>
        CCFormula(IFormulaITE(c.toFormula, l.toFormula, right.toFormula),
                  CCBool, srcInfo)
      case (c@CCFormula(_, _, _), l@CCFormula(_,_,_), r@CCFormula(_,_,_)) =>
        CCFormula(IFormulaITE(c.toFormula, l.toFormula, right.toFormula),
                  CCBool, srcInfo)
      case _ =>
        throw new ACSLParseException(
          s"""Do not know how to parse ${printer print expr}.
            | Ternary expression must be in one of the following forms:
            |   term ? term : term -> term
            |   term ? pred : pred -> pred
            |   pred ? pred : pred -> pred""".stripMargin, srcInfo.get)
    }
  }

//  def translate(pred : AST.PredLocalBinding) : IFormula = {
//    val ident   : String = pred.id_
//    val boundTo : CCExpr = translate(pred.term_)
//
//    locals.put(ident, CCTerm(boundTo.toTerm, boundTo.typ, boundTo.srcInfo))
//    val inner : IFormula = translate(pred.predicate_)
//    locals.remove(ident)
//    inner
//  }

  /* TODO: Requires all translate to just return IExpression - desired?
           Alternative approach could be preprocessing/replacement.
  def translate(pred : AST.PredLocalBinding2) : IFormula = {
    val ident   : String   = pred.id_
    val boundTo : IFormula = translate(pred.predicate_1)
    locals.put(ident, boundTo)
    val inner : IFormula = translate(pred.predicate_2)
    locals.remove(ident)
    inner
  }*/

  // TODO: Not tested. Unsure if correct.
  def translateQuantified(pred : AST.Expr) : CCFormula = {
    val srcInfo = getSourceInfo(pred)
    val (binders, bodyExpr, quantifier) = pred match {
      case expr : AST.EForAll =>
        (expr.listbinder_, expr.expr_, IExpression.Quantifier.ALL)
      case expr : AST.EExists =>
        (expr.listbinder_, expr.expr_, IExpression.Quantifier.EX)
      case _ =>
        throw new ACSLParseException(
          "Not a quantified expression: " + (printer print pred), srcInfo)
    }

    val namedTerms : Seq[(String, CCTerm)] = bindersToConstants(binders)

    namedTerms.map(t => locals.put(t._1, t._2))
    val inner : CCFormula = translatePred(bodyExpr)
    val (names, terms) : (Seq[String], Seq[CCTerm]) = namedTerms.unzip
    // FIXME: If v is shadowed, this will remove the shadowed term.
    names.map(locals.remove)

    // FIXME: Look over order of creation here.
    CCFormula(terms.foldLeft(inner.toFormula)((formula, term) => {
        val sort : Sort = term.typ.toSort
        ISortedQuantified(quantifier, sort, formula)
    }), CCBool, Some(getSourceInfo(pred)))
  }

//  def translate(pred: AST.PredExists): IFormula = {
//    val binders: Seq[AST.ABinder] =
//      pred.listbinder_.asScala.toList.map(_.asInstanceOf[AST.ABinder])
//    val namedTerms: Seq[(String, CCTerm)] = bindersToConstants(binders)
//
//    namedTerms.map(t => locals.put(t._1, t._2))
//    val inner: IFormula = translate(pred.predicate_)
//    val (names, terms): (Seq[String], Seq[CCTerm]) = namedTerms.unzip
//    // FIXME: If v is shadowed, this will remove the shadowed term.
//    names.map(locals.remove)
//
//    // FIXME: Look over order of creation here.
//    // FIXME: Use IExpression.all?
//    terms.foldLeft(inner)((formula, term) => {
//      val sort: Sort = term.typ.toSort
//      ISortedQuantified(IExpression.Quantifier.EX, sort, formula)
//    })
//  }

  private def bindersToConstants(binders : AST.ListBinder) : Seq[(String, CCTerm)] = {
    binders.asScala.toList.map(_.asInstanceOf[AST.ABinder]).flatMap(b => {
      val ctyp : CCType = getType(b.typename_)
      val idents : Seq[AST.VarIdent] = b.listvarident_.asScala.toList
      idents.map {
        case v: AST.VarIdentId =>
          (v.id_, CCTerm(ISortedVariable(0, ctyp.toSort), ctyp, None)) // todo: line no?
        case v: AST.VarIdentPtrDeref => throwNotImpl(v)
        case v: AST.VarIdentArray => throwNotImpl(v)
      }
    })
  }

  private def getType(typ : AST.TypeName) : CCType = typ match {
    case typ : AST.TypeNameLogic => getType(typ.logictypename_)
    case typ : AST.TypeNameC => getType(typ.ctypename_)
  }

  private def getType(typ : AST.LogicTypeName) : CCType = typ
    .asInstanceOf[AST.LogicTypeNameBuiltIn].builtinlogictype_ match {
    case _ : AST.BuiltInLogicTypeBoolean => CCBool
    case _ : AST.BuiltInLogicTypeInteger => CCMathInt
    case _ : AST.BuiltInLogicTypeReal => throwNotImpl("real")
  }

  private def getType(typ : AST.CTypeName) : CCType = {
    val declSpecs = typ.asInstanceOf[AST.ACTypeName].listcdeclspec_.asScala.toList
    getType(for (specifier <- declSpecs.iterator;
                 if (specifier.isInstanceOf[AST.CType]))
            yield specifier.asInstanceOf[AST.CType].ctypespec_)
  }

  private def getType(specs : Iterator[AST.CTypeSpec]) : CCType = {
    // by default assume that the type is int
    var typ : CCType = CCInt

    for (specifier <- specs)
      specifier match {
        case _ : AST.Tvoid                   => typ = CCVoid
        case _ : AST.Tint                    => // ignore
        case _ : AST.Tchar                   => // ignore
        case _ : AST.Tsigned                 => typ = CCInt
        case _ : AST.Tunsigned               => typ = CCUInt
        case _ : AST.Tlong if typ == CCInt   => typ = CCLong
        case _ : AST.Tlong if typ == CCUInt  => typ = CCULong
        case _ : AST.Tlong if typ == CCLong  => typ = CCLongLong
        case _ : AST.Tlong if typ == CCULong => typ = CCULongLong
        case e : AST.Tcollection =>
          throw new ACSLParseException(
            s"type ${printer print e} is currently not supported in ACSL" +
            s" contracts.", getSourceInfo(e))
//          val structName = getStructName(structOrUnion)
//          typ = structDefs get structName match {
//            case None             => throw new TranslationException(
//              "struct " + structName + " not found!")
//            case Some(structType) => structType
//          }
//        case enum : AST.Tenum                =>
//          typ = getEnumType(enum)
        case x => throw new ACSLParseException(
          s"type ${printer print x} not supported.", getSourceInfo(x))
      }
    typ
  }

  // `INamedPart` relevant?
//  def translate(pred : AST.PredSyntacticNaming) : IFormula = {
//    translate(pred.predicate_)
//  }

//  def translate(pred : AST.PredSyntacticNaming2) : IFormula = {
//    translate(pred.predicate_)
//  }

  // todo: this probably should work for statement annotations too
  def translateValidExpr(expr : AST.EValid) : CCFormula = {
    val srcInfo = getSourceInfo(expr)
    val tSets : List[AST.TSet] =
      expr.listlocation_.asScala.toList.map(_.asInstanceOf[AST.ALocation].tset_)
    val terms : List[CCExpr] = tSets.collect({
      case t : AST.TSetTerm  => translateTerm(t.expr_)
      case t => throwNotImpl(t)
    })

    // FIXME: Typecheck terms?
    val res = terms.foldLeft(IBoolLit(true) : IFormula)((formula, term) =>
      term.typ match {
        // FIXME: Handle CCPointer in general? (Need access to field `typ`)
        case p : CCHeapPointer =>
          import ap.parser.IExpression.{toFunApplier, toPredApplier}
          val sort : Sort = p.typ.toSort
          val heap : ITerm = ctx.getOldHeapTerm
          val valid    : IFormula = ctx.getHeap.isAlloc(heap, term.toTerm)
          val readObj  : IFunApp  = ctx.getHeap.read(heap, term.toTerm)
          val corrSort : IFormula =
            ctx.getHeap.heapADTs.hasCtor(readObj, ctx.getCtor(sort))
          formula &&& valid & corrSort
        case t =>
          throw new ACSLParseException(
            s"$t in \\valid not a heap pointer.", srcInfo)
      }
    )
    CCFormula(res, CCBool, Some(getSourceInfo(expr)))
  }

  def translateIdentExpr(t : AST.EIdent) : CCTerm = {
    val srcInfo = getSourceInfo(t)
    val ident = t.id_
    // TODO: Lookup if var exists as as local binding.
    // FIXME: Order of lookups (priority)?

    val maybeTerm = ctx match {
      case stmCtx: StatementAnnotationContext =>
        stmCtx.getTermInScope(ident)
      case _ => None
    }

    maybeTerm match {
      case Some(t) => t
      case None =>
        val bound: Option[CCTerm] = locals.get(ident)
        val scoped: Option[CCTerm] =
          vars.get(ident).map(v => CCTerm(v.term, v.typ, v.srcInfo))
        bound.getOrElse(
          scoped.getOrElse(throw new ACSLParseException(
            s"Identifier $ident not found in scope.", srcInfo)
          )
        )
    }
  }

  def translateUnary(expr : AST.EUnary) : CCExpr = {
    // FIXME: Probably needs type conversions.
    val srcInfo = getSourceInfo(expr)
    expr.unaryop_ match {
      case _ : AST.UnaryPlus =>
        translateTerm(expr.expr_)
      case _ : AST.UnaryMinus           =>
        val t = translateTerm(expr.expr_)
        CCTerm(- t.toTerm, t.typ, t.srcInfo)
      case _ : AST.UnaryNegation =>
        translate(expr.expr_) match {
          case term : CCTerm =>
            CCTerm(- term.toTerm, term.typ, term.srcInfo)
          case pred : CCFormula =>
            CCFormula(!pred.toFormula, pred.typ, pred.srcInfo)
        }
      case op : AST.UnaryComplementation => throwNotImpl(op)
      case _ : AST.UnaryPtrDeref =>
        val t = translateTerm(expr.expr_)
        t.typ match {
          case p : CCHeapPointer =>
            import ap.parser.IExpression.toFunApplier
            val heap : ITerm =
              if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
            val readObj : IFunApp = ctx.getHeap.read(heap, t.toTerm)
            val getObj  : IFunction = ctx.sortGetter(p.typ.toSort).getOrElse(
                throw new ACSLParseException(
                  s"Cannot dereference pointer of type ${p.typ}.", srcInfo)
              )
            CCTerm(getObj(readObj), p.typ, t.srcInfo)
          case p => throwNotImpl(p) // FIXME: Handle stackptr
        }
      case op : AST.UnaryAddressOf => throwNotImpl(op)
        //IFunApp(ctx.getHeap.nthAddr, Seq(ctx.getHeapTerm, right))
    }
  }

  // todo: move heap getters to Context from FunctionContext, these should be usable from statement annoations too
  //  otherwise we cannot use array accesses inside assertions.
  def translateArrayAccessExpr(term : AST.EArrayAccess) : CCTerm = {
    import ap.parser.IExpression.toFunApplier
    val srcInfo = getSourceInfo(term)
    // TODO: Untested
    val array = translateTerm(term.expr_1)
    val index = translateTerm(term.expr_2)
    array.typ match {
      case p : CCHeapPointer =>
        val heap: ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
        val access: IFunApp = ctx.getHeap.nth(array.toTerm, index.toTerm)
        val readObj: IFunApp = ctx.getHeap.read(heap, access)
        val getObj: IFunction = ctx.sortGetter(p.typ.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].", srcInfo)
        )
        CCTerm(getObj(readObj), p.typ, array.srcInfo)
      case p : CCHeapArrayPointer =>
        val heap: ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
        val access: IFunApp = ctx.getHeap.nth(array.toTerm, index.toTerm)
        val readObj: IFunApp = ctx.getHeap.read(heap, access)
        val getObj: IFunction = ctx.sortGetter(p.elementType.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].", srcInfo)
        )
        CCTerm(getObj(readObj), p.elementType, array.srcInfo)
      case p : CCArray => // todo: currently does not use wrappers, should match the encoding in CCReader
        val readObj: IFunApp = p.arrayTheory.select(array.toTerm, index.toTerm)
        val getObj: IFunction = ctx.sortGetter(p.elementType.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].", srcInfo)
        )
        //CCTerm(getObj(readObj), p.elementType, array.srcInfo)
        CCTerm(readObj, p.elementType, array.srcInfo)
      case _ =>
        throw new ACSLParseException("Array access could not be handled.", srcInfo)
    }
  }

  def translateStructFieldAccessExpr(expr: AST.EStructFieldAccess) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    val subExpr = translate(expr.expr_)
    val fieldName = expr.id_
    subExpr.typ match {
      case struct : CCStruct =>
        struct.getFieldIndex(fieldName) match {
          case -1 =>
            throw new ACSLParseException(
              s"$fieldName is not a field of $struct: ${printer.print(expr)}", srcInfo)
          case fieldInd =>
            val fieldSelector = struct.getADTSelector(fieldInd)
            val fieldTyp = struct.getFieldType(fieldInd)
            CCTerm(IFunApp(fieldSelector, Seq(subExpr.toTerm)),
                   fieldTyp, Some(srcInfo))
        }
      case _ =>
        throw new ACSLParseException(
          s"Tried to access $expr but $subExpr is not a struct.", srcInfo)
    }
  }

  def translateOldExpr(expr : AST.EOld) : CCTerm = {
    val old = vars
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ funCtx.getGlobals.map(v => (v.name, funCtx.getOldVar(v.name).get))).toMap
    useOldHeap = true
    val res = translateTerm(expr.expr_)
    useOldHeap = false
    vars = old
    res
  }

  def translateResultExpr(expr : AST.EResult) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    val funCtx = ctx.asInstanceOf[FunctionContext]
    if (!inPostCond) {
      throw new ACSLParseException("\\result has no meaning.", srcInfo)
    }

    funCtx.getResultVar.map(v => CCTerm(v.term, v.typ, v.srcInfo))
      .getOrElse(
        throw new ACSLParseException("\\result used in void function.", srcInfo)
      )
  }

  private def throwNotImpl[T](obj : T) = {
    throw new NotImplementedError(s"ACSL support missing for ${obj.getClass}.")
  }
}
