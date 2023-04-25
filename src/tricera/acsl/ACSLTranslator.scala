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
import ap.parser.IExpression
import ap.parser.{IBoolLit, IConstant, IFormula, IFormulaITE, IFunApp, IFunction, ISortedQuantified, ISortedVariable, ITerm}
import ap.theories.nia.GroebnerMultiplication._
import ap.types.{Sort, SortedConstantTerm}
import ap.theories.Heap
import tricera.Util.{SourceInfo, getSourceInfo}
import tricera.acsl.Absyn.LoopInvSimple
import tricera.concurrency.ccreader._
import CCExceptions._

class ACSLParseException(msg : String) extends Exception(msg)
class ACSLTranslateException(msg : String) extends Exception(msg)

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
               col    = srcInfo.col ,
               offset = begin.offset + srcInfo.offset)
  }

  def translateACSL(annot : String,
                    ctx   : AnnotationContext) : ParsedAnnotation = {
    val l : Yylex = new Yylex(new java.io.StringReader(preprocess(annot)))
    val p : parser = new parser(l, l.getSymbolFactory())
    try {
      val ast : AST.Annotation = p.pAnnotation()
      val translator = new ACSLTranslator(ctx)

      ast match {
        case ac : AST.AnnotContract =>
          ctx match {
            case funCtx : FunctionContext =>
              translator.translate(ac.functioncontract_)
            case _ => throw new ACSLParseException("A function context is " +
              "needed to parse a function contract.")
          }
        case ac : AST.AnnotAssertion =>
          ctx match {
            case stmCtx : StatementAnnotationContext =>
              translator.translate(ac.assertion_, stmCtx)
            case _ => throw new ACSLParseException("A statement context is " +
              "needed to parse a statement annotation.")
          }
        case ac : AST.LoopAnnot =>
          ctx match {
            case stmCtx : StatementAnnotationContext =>
              translator.translate(ac.loopinvariant_, stmCtx)
            case _ => throw new ACSLParseException("A statement context is " +
              "needed to parse a loop invariant annotation.")
          }
        case _ => throw new ACSLParseException("Not a contract or " +
          "statement annotation.")
      }
    } catch {
      case NeedsHeapModelException =>
        throw NeedsHeapModelException
      case e : Exception =>
        e.printStackTrace()
        throw new ACSLParseException(
          "At line " + String.valueOf(getActualLine(ctx, l.line_num())) +
          ", near \"" + l.buff() + "\" :" +
          "     " + e.getMessage()
        )
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

class ACSLTranslator(ctx   : ACSLTranslator.AnnotationContext) {
  import scala.collection.mutable.{HashMap => MHashMap}
  import ACSLTranslator._

  val locals = new MHashMap[String, CCTerm]
  var vars: Map[String, CCVar] = Map()
  var inPostCond = false
  var useOldHeap = false
  // TODO: Make all `translate` private?

  // ---- Statement annotations (e.g., assertions) -----------
  def translate(assertAnnotation : AST.Assertion,
                stmCtx           : StatementAnnotationContext) : StatementAnnotation = {
    assertAnnotation match {
      case regularAssertion : AST.RegularAssertion1 =>
            val f = translate(regularAssertion.predicate_)
            StatementAnnotation(f, isAssert = true)
      case regularAssertion: AST.RegularAssertion2 =>
        val f = translate(regularAssertion.predicate_)
        StatementAnnotation(f, isAssert = true)
      case _ =>
        throw new ACSLParseException("Behaviour assertions are " +
          "currently unsupported.")
    }
  }

  // ---- Loop annotations -----------------------------------
  def translate(loopInvariantAnnotation : AST.LoopInvariant,
                stmCtx                  : StatementAnnotationContext)
  : LoopAnnotation = {
    loopInvariantAnnotation match {
      case inv : LoopInvSimple =>
        val f = translate(inv.predicate_)
        LoopAnnotation(f)
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
          case _ => throw new ACSLParseException("Unsupported simple clause.")
        }

      // NOTE: `pre` and `post` defaults to true given usage of `and`.
      useOldHeap = true
      val pre  : IFormula = IExpression.and(rcs.map(f => translate(f)))
      useOldHeap = false
      val post : IFormula = IExpression.and(ecs.map(f => translate(f)))

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
            t.term_ match {
              case i : AST.TermIdent => (translate(i) :: idents, ptrDerefs)
              case p : AST.TermUnaryOp
                if p.unaryop_.isInstanceOf[AST.UnaryOpPtrDeref] => {
                useOldHeap = true
                val res = (idents, translate(p.term_) :: ptrDerefs)
                useOldHeap = false
                res
              }
            case _ => throw new ACSLParseException("Only global identifiers or "
              + "heap pointer dereferences allowed in assigns-clauses.")
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
  def translate(clause : AST.SimpleClause) : IFormula = clause match {
    case ac : AST.SimpleClauseAssigns => throwNotImpl(ac)
    case ec : AST.SimpleClauseEnsures => translate(ec.ensuresclause_)
  }


  def translate(clause : AST.EnsuresClause) : IFormula = {
    val funCtx = ctx.asInstanceOf[FunctionContext]
    inPostCond = true
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, v))).toMap
    val res = translate(clause.asInstanceOf[AST.AnEnsuresClause].predicate_)
    inPostCond = false
    res
  }

  def translate(clause : AST.RequiresClause) : IFormula = {
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams ++ ctx.getGlobals).map(v =>
      (v.name, funCtx.getOldVar(v.name).get)).toMap
    translate(clause.asInstanceOf[AST.ARequiresClause].predicate_)
  }

  // ---- Predicates -----------------------------------------
  def translate(pred : AST.Predicate) : IFormula = pred match {
    case p : AST.PredTrue             => translate(p)
    case p : AST.PredFalse            => translate(p)
    case p : AST.PredRelOp            => translate(p)
    case p : AST.PredApplication      => throwNotImpl(p) // Redundant for now.
    case p : AST.PredParentheses      => translate(p)
    case p : AST.PredConjunction      => translate(p)
    case p : AST.PredDisjunction      => translate(p)
    case p : AST.PredImplication      => translate(p)
    case p : AST.PredEquivalence      => translate(p)
    case p : AST.PredNegation         => translate(p)
    case p : AST.PredXOr              => translate(p)
    case p : AST.PredTernaryCond      => throwNotImpl(p)
    case p : AST.PredTernaryCond2     => translate(p)
    case p : AST.PredLocalBinding     => translate(p)
    case p : AST.PredLocalBinding2    => throwNotImpl(p)
    case p : AST.PredForAll           => translate(p)
    case p : AST.PredExists           => translate(p)
    case p : AST.PredSyntacticNaming  => translate(p)
    case p : AST.PredSyntacticNaming2 => translate(p)
    case p : AST.PredOld              => throwNotImpl(p)
    case p : AST.PredValid            => translate(p)
  }

  def translate(pred : AST.PredTrue) : IFormula = {
    IBoolLit(true)
  }

  def translate(pred : AST.PredFalse) : IFormula = {
    IBoolLit(false)
  }

  def translate(pred : AST.PredRelOp) : IFormula = {
    val left  : ITerm = translate(pred.term_1).toTerm
    val right : ITerm = translate(pred.term_2).toTerm
    pred.relop_ match {
      case op : AST.RelOpEQ  => left === right
      case op : AST.RelOpNEQ => left =/= right
      case op : AST.RelOpLEQ => left <= right
      case op : AST.RelOpGEQ => left >= right
      case op : AST.RelOpGT  => left > right
      case op : AST.RelOpLT  => left < right
    }
  }

  def translate(pred : AST.PredParentheses) : IFormula = {
    translate(pred.predicate_)
  }

  // NOTE: Might wanna simplify directly with e.g. &&&.
  def translate(pred : AST.PredConjunction) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left & right
  }

  def translate(pred : AST.PredDisjunction) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left | right
  }

  def translate(pred : AST.PredImplication) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left ==> right
  }

  def translate(pred : AST.PredEquivalence) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left <=> right
  }

  def translate(pred : AST.PredNegation) : IFormula = {
    val right : IFormula = translate(pred.predicate_)
    !right
  }

  def translate(pred : AST.PredXOr) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left </> right
  }

  // How will this clash with `PredTernaryCond`?
  def translate(pred : AST.PredTernaryCond2) : IFormula = {
    val cond  : IFormula = translate(pred.predicate_1)
    val left  : IFormula = translate(pred.predicate_2)
    val right : IFormula = translate(pred.predicate_3)
    IFormulaITE(cond, left, right)
  }

  def translate(pred : AST.PredLocalBinding) : IFormula = {
    val ident   : String = pred.id_
    val boundTo : CCExpr = translate(pred.term_)

    locals.put(ident, CCTerm(boundTo.toTerm, boundTo.typ, boundTo.srcInfo))
    val inner : IFormula = translate(pred.predicate_)
    locals.remove(ident)
    inner
  }

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
  def translate(pred : AST.PredForAll) : IFormula = {
    val binders : Seq[AST.ABinder] =
      pred.listbinder_.asScala.toList.map(_.asInstanceOf[AST.ABinder])
    val namedTerms : Seq[(String, CCTerm)] = bindersToConstants(binders)

    namedTerms.map(t => locals.put(t._1, t._2))
    val inner : IFormula = translate(pred.predicate_)
    val (names, terms) : (Seq[String], Seq[CCTerm]) = namedTerms.unzip
    // FIXME: If v is shadowed, this will remove the shadowed term.
    names.map(locals.remove)

    // FIXME: Look over order of creation here.
    // FIXME: Use IExpression.all?
    terms.foldLeft(inner)((formula, term) => {
        val sort : Sort = term.typ.toSort
        ISortedQuantified(IExpression.Quantifier.ALL, sort, formula)
    })
  }

  def translate(pred: AST.PredExists): IFormula = {
    val binders: Seq[AST.ABinder] =
      pred.listbinder_.asScala.toList.map(_.asInstanceOf[AST.ABinder])
    val namedTerms: Seq[(String, CCTerm)] = bindersToConstants(binders)

    namedTerms.map(t => locals.put(t._1, t._2))
    val inner: IFormula = translate(pred.predicate_)
    val (names, terms): (Seq[String], Seq[CCTerm]) = namedTerms.unzip
    // FIXME: If v is shadowed, this will remove the shadowed term.
    names.map(locals.remove)

    // FIXME: Look over order of creation here.
    // FIXME: Use IExpression.all?
    terms.foldLeft(inner)((formula, term) => {
      val sort: Sort = term.typ.toSort
      ISortedQuantified(IExpression.Quantifier.EX, sort, formula)
    })
  }

  private def bindersToConstants(binders : Seq[AST.ABinder]) : Seq[(String, CCTerm)] = {
    binders.flatMap(b => {
      val typ : AST.CTypeSpecifier =
        b.typename_.asInstanceOf[AST.TypeNameC].ctypespecifier_
      val ctyp : CCType = toCCType(typ)
      val idents : Seq[AST.VariableIdent] = b.listvariableident_.asScala.toList
      idents.map {
        case v: AST.VariableIdentId =>
          (v.id_, CCTerm(ISortedVariable(0, ctyp.toSort), ctyp, None)) // todo: line no?
        case v: AST.VariableIdentPtrDeref => throwNotImpl(v)
        case v: AST.VariableIdentArray => throwNotImpl(v)
        case v: AST.VariableIdentParentheses => throwNotImpl(v)
      }
    })
  }

  private def toCCType(typ : AST.CTypeSpecifier) : CCType = typ match {
    case t : AST.CTypeSpecifierVoid     => throwNotImpl(t)
    case t : AST.CTypeSpecifierChar     => throwNotImpl(t)
    case t : AST.CTypeSpecifierShort    => throwNotImpl(t)
    case t : AST.CTypeSpecifierInt      => CCInt
    case t : AST.CTypeSpecifierLong     => throwNotImpl(t)
    case t : AST.CTypeSpecifierFloat    => throwNotImpl(t)
    case t : AST.CTypeSpecifierDouble   => throwNotImpl(t)
    case t : AST.CTypeSpecifierSigned   => throwNotImpl(t)
    case t : AST.CTypeSpecifierUnsigned => throwNotImpl(t)
    case t : AST.CTypeSpecifierStruct   => throwNotImpl(t)
    case t : AST.CTypeSpecifierUnion    => throwNotImpl(t)
    case t : AST.CTypeSpecifierEnum     => throwNotImpl(t)
    case t : AST.CTypeSpecifierId       => throwNotImpl(t)
  }

  // `INamedPart` relevant?
  def translate(pred : AST.PredSyntacticNaming) : IFormula = {
    translate(pred.predicate_)
  }

  def translate(pred : AST.PredSyntacticNaming2) : IFormula = {
    translate(pred.predicate_)
  }

  // todo: this probably should work for statement annotations too
  def translate(pred   : AST.PredValid) : IFormula = {
    val tSets : List[AST.TSet] =
      pred.listlocation_.asScala.toList.map(_.asInstanceOf[AST.ALocation].tset_)
    val terms : List[CCExpr] = tSets.collect({
      case t : AST.TSetTerm  => translate(t.term_)
      case t => throwNotImpl(t)
    })

    // FIXME: Typecheck terms?
    terms.foldLeft(IBoolLit(true) : IFormula)((formula, term) =>
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
          throw new ACSLParseException(s"$t in \\valid not a heap pointer.")
      }
    )
  }

  // ---- Terms ----------------------------------------------
  def translate(term : AST.Term) : CCExpr = term match {
    case t : AST.TermLiteral                 => translate(t)
    case t : AST.TermIdent                   => translate(t)
    case t : AST.TermUnaryOp                 => translate(t)
    case t : AST.TermBinOp                   => translate(t)
    case t : AST.TermArrayAccess             => translate(t)
    case t : AST.TermArrayFunctionalModifier => throwNotImpl(t)
    case t : AST.TermStructFieldAccess       => throwNotImpl(t)
    case t : AST.TermFieldFunctionalModifier => throwNotImpl(t)
    case t : AST.TermStructPtrFieldAccess    => throwNotImpl(t)
    case t : AST.TermTypeCast                => throwNotImpl(t)
    case t : AST.TermFuncAppl                => throwNotImpl(t)
    case t : AST.TermParentheses             => translate(t)
    case t : AST.TermTernaryCond             => throwNotImpl(t)
    case t : AST.TermLocalBinding            => throwNotImpl(t)
    case t : AST.TermSizeOfTerm              => throwNotImpl(t)
    case t : AST.TermSizeOfType              => throwNotImpl(t)
    case t : AST.TermSyntacticNaming         => throwNotImpl(t)
    case t : AST.TermSyntacticNaming2        => throwNotImpl(t)
    case t : AST.TermOld                     => translate(t)
    case t : AST.TermResult                  => translate(t)
  }

  def translate(term : AST.TermLiteral) : CCTerm = {
    translate(term.literal_)
  }

  def translate(t : AST.TermIdent) : CCTerm = {
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
          scoped.getOrElse(
            throw new ACSLParseException(s"Identifier $ident not found in scope.")
          )
        )
    }
  }

  def translate(term : AST.TermUnaryOp) : CCExpr = {
    val right : CCExpr = translate(term.term_)
    // FIXME: Probably needs type conversions.
    term.unaryop_ match {
      case op : AST.UnaryOpPlus            => throwNotImpl(op)
      case op : AST.UnaryOpMinus           =>
        CCTerm(right.toTerm.unary_-, right.typ, right.srcInfo)
      case op : AST.UnaryOpNegation =>
        CCTerm(right.toTerm.unary_-, right.typ, right.srcInfo)
      case op : AST.UnaryOpComplementation => throwNotImpl(op)
      case op : AST.UnaryOpPtrDeref =>
        right.typ match {
          case p : CCHeapPointer =>
            import ap.parser.IExpression.toFunApplier
            val heap : ITerm =
              if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
            val readObj : IFunApp = ctx.getHeap.read(heap, right.toTerm)
            val getObj  : IFunction = ctx.sortGetter(p.typ.toSort).getOrElse(
                throw new ACSLParseException(
                  s"Cannot dereference pointer of type ${p.typ}."
                )
              )
            CCTerm(getObj(readObj), p.typ, right.srcInfo)
          // FIXME: Handle stackptr
          case p => throwNotImpl(p)
        }
      case op : AST.UnaryOpAddressOf => throwNotImpl(op)
        //IFunApp(ctx.getHeap.nthAddr, Seq(ctx.getHeapTerm, right))
    }
  }

  def translate(term : AST.TermBinOp) : CCExpr = {
    val left  : CCExpr = translate(term.term_1)
    val right : CCExpr = translate(term.term_2)
    // FIXME: Type promotion?
    //assert(left.typ == right.typ)
    val typ : CCType = left.typ
    val srcInfo = left.srcInfo
    term.binop_ match {
      case op : AST.BinOpPlus =>
        CCTerm(left.toTerm + right.toTerm, typ, srcInfo)
      case op : AST.BinOpMinus =>
        CCTerm(left.toTerm - right.toTerm, typ, srcInfo)
      case op : AST.BinOpMult =>
        CCTerm(mult(left.toTerm, right.toTerm), typ, srcInfo)
      case op : AST.BinOpDiv =>
        CCTerm(tDiv(left.toTerm, right.toTerm), typ, srcInfo)
      case op : AST.BinOpMod =>
        CCTerm(tMod(left.toTerm, right.toTerm), typ, srcInfo)
      case _ : AST.BinOpEQ           =>
        CCFormula(left.toTerm === right.toTerm, typ, srcInfo)
      case _ : AST.BinOpNEQ          =>
        CCFormula(left.toTerm =/= right.toTerm, typ, srcInfo)
      case _ : AST.BinOpLEQ          => // todo: this mixes and matches terms and formulas right now! needs parentheses everywhere to work correctly
        CCFormula(left.toTerm <= right.toTerm, typ, srcInfo)
      case _ : AST.BinOpGEQ          =>
        CCFormula(left.toTerm >= right.toTerm, typ, srcInfo)
      case op : AST.BinOpGT           =>
        CCFormula(left.toTerm > right.toTerm, typ, srcInfo)
      case op : AST.BinOpLT           =>
        CCFormula(left.toTerm < right.toTerm, typ, srcInfo)
      case op : AST.BinOpAnd          =>
        CCFormula(left.toFormula &&& right.toFormula, typ, srcInfo)
      case op : AST.BinOpOr           =>
        CCFormula(left.toFormula ||| right.toFormula, typ, srcInfo)
      case op : AST.BinOpXOr          =>
        CCFormula((left.toFormula &&& !right.toFormula) |||
          (!left.toFormula &&& right.toFormula), typ, srcInfo)
      case op : AST.BinOpLShift       => throwNotImpl(op)
      case op : AST.BinOpRShift       => throwNotImpl(op)
      case op : AST.BinOpBitwiseAnd   => throwNotImpl(op)
      case op : AST.BinOpBitwiseOr    => throwNotImpl(op)
      case op : AST.BinOpBitwiseImpl  => throwNotImpl(op)
      case op : AST.BinOpBitwiseEquiv => throwNotImpl(op)
      case op : AST.BinOpBitwiseXOr   => throwNotImpl(op)
    }
  }

  // todo: move heap getters to Context from FunctionContext, these should be usable from statement annoations too
  //  otherwise we cannot use array accesses inside assertions.
  def translate(term : AST.TermArrayAccess) : CCExpr = {
    import ap.parser.IExpression.toFunApplier
    // TODO: Unsure if working.
    val array : CCExpr = translate(term.term_1)
    val index : CCExpr = translate(term.term_2)
    array.typ match {
      case p : CCHeapPointer =>
        val heap: ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
        val access: IFunApp = ctx.getHeap.nth(array.toTerm, index.toTerm)
        val readObj: IFunApp = ctx.getHeap.read(heap, access)
        val getObj: IFunction = ctx.sortGetter(p.typ.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].")
        )
        CCTerm(getObj(readObj), p.typ, array.srcInfo)
      case p : CCHeapArrayPointer =>
        val heap: ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
        val access: IFunApp = ctx.getHeap.nth(array.toTerm, index.toTerm)
        val readObj: IFunApp = ctx.getHeap.read(heap, access)
        val getObj: IFunction = ctx.sortGetter(p.elementType.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].")
        )
        CCTerm(getObj(readObj), p.elementType, array.srcInfo)
      case p : CCArray => // todo: currently does not use wrappers, should match the encoding in CCReader
        val readObj: IFunApp = p.arrayTheory.select(array.toTerm, index.toTerm)
        val getObj: IFunction = ctx.sortGetter(p.elementType.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].")
        )
        //CCTerm(getObj(readObj), p.elementType, array.srcInfo)
        CCTerm(readObj, p.elementType, array.srcInfo)
      case _ =>
        throw new ACSLParseException("Array access could not be handled.")
    }
  }

  def translate(term : AST.TermParentheses) : CCExpr = {
    translate(term.term_)
  }

  def translate(term : AST.TermOld) : CCExpr = {
    val old = vars
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ funCtx.getGlobals.map(v => (v.name, funCtx.getOldVar(v.name).get))).toMap
    useOldHeap = true
    val res = translate(term.term_)
    useOldHeap = false
    vars = old
    res
  }

  def translate(term   : AST.TermResult) : CCExpr = {
    val funCtx = ctx.asInstanceOf[FunctionContext]
    if (!inPostCond) {
      throw new ACSLParseException("\\result has no meaning.")
    }

    funCtx.getResultVar.map(v => CCTerm(v.term, v.typ, v.srcInfo))
      .getOrElse(
        throw new ACSLParseException("\\result used in void function.")
      )
  }

  // ---- Literals -------------------------------------------
  def translate(literal : AST.Literal) : CCTerm = literal match {
    // Do we want to use CCTypes here or what?
    case l : AST.LiteralTrue   => throwNotImpl(l) // IBoolLit(true)
    case l : AST.LiteralFalse  => throwNotImpl(l) // IBoolLit(false)
    case l : AST.LiteralInt    =>
      import ap.basetypes.IdealInt
      val term : ITerm = IExpression.i(IdealInt(l.unboundedinteger_))
      CCTerm(term, CCInt, None) // todo; line no?
    case l : AST.LiteralReal   => throwNotImpl(l)
    case l : AST.LiteralString => throwNotImpl(l) // ap.theories.string.StringTheory?
    case l : AST.LiteralChar   => throwNotImpl(l)
  }

  private def throwNotImpl[T](obj : T) = {
    throw new NotImplementedError(s"Support missing for ${obj.getClass}.")
  }
}
