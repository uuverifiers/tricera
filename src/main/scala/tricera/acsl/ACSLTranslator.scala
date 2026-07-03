/**
 * Copyright (c) 2021-2022 Pontus Ernstedt
 *               2022-2026 Zafer Esen. All rights reserved.
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

import scala.jdk.CollectionConverters._
import ap.parser._
import ap.theories.nia.GroebnerMultiplication._
import ap.types.{Sort, SortedConstantTerm}
import ap.theories.heaps.Heap
import tricera.Util.{SourceInfo, getSourceInfo}
import tricera.concurrency.ccreader._
import tricera.Literals
import CCExceptions._

class ACSLException(msg : String) extends Exception(msg)
class ACSLParseException(msg : String, srcInfo : SourceInfo) extends Exception(msg)

object ACSLTranslator {

  trait AnnotationContext {
    def getGlobals : Seq[CCVar]
    def sortWrapper(s: Sort): Option[IFunction]
    def sortGetter(s: Sort): Option[IFunction]
    def wrapperSort(wrapper: IFunction): Option[Sort]
    def getterSort(getter: IFunction): Option[Sort]
    def getCtor(s: Sort): Int
    def getTypOfPointer(t: CCType): CCType
    def isHeapEnabled: Boolean
    def getHeap: Heap
    def getHeapTerm: ITerm
    def getOldHeapTerm : ITerm
    val getStructMap: Map[IFunction, CCStruct]
    val annotationBeginSourceInfo : SourceInfo
    val annotationNumLines : Int
    def enumeratorDefs : scala.collection.Map[String, CCTerm] = Map.empty
    def acslPredicateDefs : scala.collection.Map[String, PredicateDef] = Map.empty
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

  // The ACSL state that \at(e, id) refers to (ACSL v1.23, Table 2.1)
  sealed abstract class Label
  object Label {
    case object Here        extends Label
    case object Pre         extends Label
    case object Old         extends Label
    case object Post        extends Label
    case object Init        extends Label
    case object LoopEntry   extends Label
    case object LoopCurrent extends Label
    final case class CLabel(name : String) extends Label

    def apply(id : String) : Label = id match {
      case "Here"        => Here
      case "Pre"         => Pre
      case "Old"         => Old
      case "Post"        => Post
      case "Init"        => Init
      case "LoopEntry"   => LoopEntry
      case "LoopCurrent" => LoopCurrent
      case name          => CLabel(name)
    }
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

  def parseToAST(annot : String) : AST.Annotation = {
    val l : Yylex = new Yylex(new java.io.StringReader(preprocess(annot)))
    val p : parser = new parser(l, l.getSymbolFactory())
    p.pAnnotation()
  }

  @throws[ACSLException]("if not called with the right context")
  @throws[ACSLParseException]("if parsing or translation fails")
  def translateACSL(annot        : String,
                    ctx          : AnnotationContext,
                    astTransform : AST.Annotation => AST.Annotation = identity)
  : ParsedAnnotation = {
    val ast : AST.Annotation = astTransform(parseToAST(annot))
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

    def normalizeUnicode(s : String) : String =
      s.replace("∀", "\\forall").replace("∃", "\\exists")
       .replace("ℤ", "integer").replace("ℝ", "real")
       .replace("⇒", "==>").replace("⇔", "<==>")
       .replace("∧", "&&").replace("∨", "||").replace("¬", "!")
       .replace("≡", "==").replace("≢", "!=").replace("≠", "!=")
       .replace("≤", "<=").replace("≥", ">=")
    normalizeUnicode(replaceAtSymbols(annot))
  }

  case class PredicateDef(name        : String,
                          labelParams : List[String],
                          valueParams : List[String],
                          body        : AST.Expr)

  def parsePredicateDef(annot : String) : PredicateDef = {
    val l = new Yylex(new java.io.StringReader(preprocess(annot)))
    val p = new parser(l, l.getSymbolFactory())
    p.pAnnotation() match {
      case ap : AST.AnnotPredicate => ap.predicatedef_ match {
        case d : AST.PredWithParams =>
          PredicateDef(d.id_, d.listid_.asScala.toList,
                       predParamNames(d.listpredparam_), d.expr_)
        case d : AST.PredNoParams =>
          PredicateDef(d.id_, d.listid_.asScala.toList, Nil, d.expr_)
      }
      case _ => throw new ACSLException("Expected a predicate definition.")
    }
  }

  private def predParamNames(ps : AST.ListPredParam) : List[String] =
    ps.asScala.toList.map {
      case p : AST.APredParam => varIdentName(p.varident_)
    }

  private def varIdentName(v : AST.VarIdent) : String = v match {
    case x : AST.VarIdentId       => x.id_
    case x : AST.VarIdentArray    => varIdentName(x.varident_)
    case x : AST.VarIdentPtrDeref => varIdentName(x.varident_)
  }

  // labels that need to be captured ahead of their use
  def isCapturedLabel(id : String) : Boolean = Label(id) match {
    case Label.Pre        => true
    case Label.CLabel(_)  => true
    case _                => false
  }

  private def copyLoc[N <: SourceInfoProvider]
                     (src : SourceInfoProvider, node : N) : N = {
    node.setLineNum(src.getLineNum)
    node.setColNum(src.getColNum)
    node.setOffset(src.getOffset)
    node
  }

  // collect captured \at nodes. EAt has structural equality
  class CaptureCollector extends ComposVisitor[Unit] {
    val found = new scala.collection.mutable.ListBuffer[AST.EAt]
    override def visit(p : AST.EAt, a : Unit) : AST.Expr =
      if (isCapturedLabel(p.id_)) { found += p; p } else super.visit(p, a)
  }

  // rewrite an \at expr using its capture variable
  class CaptureRewriter(names : Map[AST.EAt, String]) extends ComposVisitor[Unit] {
    override def visit(p : AST.EAt, a : Unit) : AST.Expr =
      if (isCapturedLabel(p.id_))
        copyLoc(p, new AST.EIdent(names(p)))
      else super.visit(p, a)
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

  // maps a predicate's label parameter to the `\at` label it is bound to
  private val labelBindings = new MHashMap[String, String]
  // a stack to detect recursive predicates (and reject them)
  private var inliningStack  : List[String] = Nil

  // ---- Statement annotations (e.g., assertions) -----------
  def translate(assertAnnotation : AST.Assertion,
                stmCtx           : StatementAnnotationContext)
  : StatementAnnotation = {
    val srcInfo = getSourceInfo(assertAnnotation)
    assertAnnotation match {
      case regularAssertion : AST.RegularAssertion =>
            val (name, body) = regularAssertion.expr_ match {
              case e : AST.ENaming1 => (Some(e.id_), e.expr_)
              case e : AST.ENaming2 => (Some(e.string_), e.expr_)
              case e                => (None, e)
            }
            val f = translate(body)
            // assert and check are proof obligations, admit is an assumption
            val isAssert = regularAssertion.assertionkind_ match {
              case nb : AST.NonBlockingAssert =>
                !nb.clausekind_.isInstanceOf[AST.ClauseKindAdmit]
              case _ => true
            }
            StatementAnnotation(f.toFormula, isAssert, name)
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
      val preClauses : Seq[(Option[String], IFormula)] =
        rcs.map(f => (reqClauseName(f), translate(f).toFormula))
      val pre  : IFormula = IExpression.and(preClauses.map(_._2))
      useOldHeap = false
      val postClauses : Seq[(Option[String], IFormula)] =
        ecs.map(f => (ensClauseName(f), translate(f).toFormula))
      val post : IFormula = IExpression.and(postClauses.map(_._2))

      // FIXME: Refactor and break out in functions!
      val assigns : (IFormula, IFormula) = acs match {
        case Nil => (IBoolLit(true), IBoolLit(true))
        case acs =>
          val (idents, ptrDerefs, arrayElems) =
            acs.foldLeft((Set[CCTerm](), Set[CCTerm](),
                          Set[(String, CCArray, CCTerm)]())) ({(sets, clause) =>
              val (i, p, a) =
                translateAssigns(clause.assignsclause_)
              (i.union(sets._1), p.union(sets._2), a.union(sets._3))
            })

          val funCtx = ctx.asInstanceOf[FunctionContext]

          val arrayElemConstraint : IFormula = {
            import ap.parser.IExpression._
            arrayElems.groupBy(_._1).foldLeft(IBoolLit(true) : IFormula) {
              case (formula, (name, elems)) =>
                val gOld  : ITerm = funCtx.getOldVar(name).get.term
                val gPost : ITerm = funCtx.getPostGlobalVar(name).get.term
                val framed = elems.foldLeft(gOld) {
                  case (h, (_, arr, idx)) =>
                    arr.arrayTheory.store(h, idx.toTerm,
                      arr.arrayTheory.select(gPost, idx.toTerm))
                }
                formula &&& (gPost === framed)
            }
          }
          val elemAssignedNames = arrayElems.map(_._1)

          val globConstraint : IFormula =
            if (idents.isEmpty && arrayElems.isEmpty) {
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
              val postGlobals : Seq[ITerm] =
                ctx.getGlobals.map(g => funCtx.getPostGlobalVar(g.name).get.term)
              val globToPost : Map[ITerm, ITerm] =
                globals.zip(postGlobals).toMap

              val elemAssignedTerms : Set[ITerm] =
                ctx.getGlobals.filter(g => elemAssignedNames contains g.name)
                  .map(g => IConstant(g.term) : ITerm).toSet
              val nonAssignedGlobals : Set[ITerm] =
                globals.toSet.diff(idents.map(_.toTerm)).diff(elemAssignedTerms)

              nonAssignedGlobals.foldLeft(IBoolLit(true) : IFormula) (
                (formula, term) => formula &&& globToPost(term) === globToOld(term)
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

                val ptrObjPairs : List[(CCTerm, ITerm)] =
                  ptrDerefs.zip(addrObjPairs.map(_._2)).toList

                val corrSort : IFormula =
                  ptrObjPairs.foldLeft(IBoolLit(true) : IFormula) (
                    (formula, pair) => {
                      val (p, obj) = pair
                      val sort : Sort =
                        p.typ.asInstanceOf[CCHeapPointer].typ.toSort
                      val corr : IFormula =
                        funCtx.getHeap.hasUserHeapCtor(obj, ctx.getCtor(sort))
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
          (heapAssert &&& globConstraint &&& arrayElemConstraint,
           heapAssume &&& globConstraint &&& arrayElemConstraint)
      }

      val postSrcInfo = ecs match {
        case Nil => getSourceInfo(c) // no post-conditions, value does not matter
        case hd :: tl => getSourceInfo(hd)
      }

      // todo: have separate line numbers for ecs
      new FunctionContract(pre, post, assigns._1, assigns._2,
                           getSourceInfo(c),
                           getActualSourceInfo(ctx, postSrcInfo),
                           preClauses, postClauses)

    case _ => throwNotImpl(contract)
  }

  // FIXME: Return ITerm directly?
  def translateAssigns(clause : AST.AssignsClause)
    : (Set[CCTerm], Set[CCTerm], Set[(String, CCArray, CCTerm)]) = {
    val srcInfo = getSourceInfo(clause)
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, v))).toMap
    val locations = clause match {
      case c : AST.AnAssignsClause     => c.locations_
      case c : AST.AnAssignsClauseFrom => c.locations_1
    }
    locations match {
      case ls : AST.LocationsSome    =>
        val tSets : List[AST.TSet] =
          ls.listlocation_.asScala.toList
          .map(_.asInstanceOf[AST.ALocation].tset_)
        val nils = (Nil : List[CCTerm], Nil : List[CCTerm],
                    Nil : List[(String, CCArray, CCTerm)])
        val terms : (List[CCTerm], List[CCTerm],
                     List[(String, CCArray, CCTerm)]) =
          tSets.foldRight(nils) ({
          case (t : AST.TSetTerm, (idents, ptrDerefs, arrayElems)) =>
            t.expr_ match {
              case i : AST.EIdent => (translate(i) :: idents, ptrDerefs, arrayElems)
              case _ : AST.EResult => (idents, ptrDerefs, arrayElems)
              case p : AST.EUnary
                if p.unaryop_.isInstanceOf[AST.UnaryPtrDeref] => {
                useOldHeap = true
                val res = (idents, translateTerm(p.expr_) :: ptrDerefs, arrayElems)
                useOldHeap = false
                res
              }
              case arr : AST.EArrayAccess => {
                import ap.parser.IExpression.toFunApplier
                useOldHeap = true
                val array = translateTerm(arr.expr_1)
                val index = translateTerm(arr.expr_2)
                useOldHeap = false
                array.typ match {
                  case p : CCHeapArrayPointer =>
                    val ops  = p.ptrOps
                    val addr = ctx.getHeap.rangeNth(
                      ops.getRange(array.toTerm),
                      ops.getOffset(array.toTerm) + index.toTerm)
                    val elemPtr = CCTerm.fromTerm(addr,
                      CCHeapPointer(ctx.getHeap.AddressSort,
                                    ctx.getHeap.nullAddr(), p.elementType),
                      array.srcInfo)
                    (idents, elemPtr :: ptrDerefs, arrayElems)
                  case a : CCArray =>
                    arr.expr_1 match {
                      case id : AST.EIdent =>
                        (idents, ptrDerefs, (id.id_, a, index) :: arrayElems)
                      case _ => throw new ACSLParseException(
                        "assigns over an element of an array modeled with " +
                        "the theory of arrays requires a global array " +
                        "identifier as the base", srcInfo)
                    }
                  case _ => throw new ACSLParseException(
                    s"Unsupported array base in assigns clause: $array.", srcInfo)
                }
              }
            case _ => throw new ACSLParseException("Only global identifiers or "
              + "heap pointer dereferences allowed in assigns-clauses.", srcInfo)
          }
          case t => throwNotImpl(t)
        })
        (terms._1.toSet, terms._2.toSet, terms._3.toSet)
      case _  : AST.LocationsNothing => (Set(), Set(), Set())
    }
  }


  // FIXME: Type is specified already.

  /**
   * Translates assigns / ensures clauses.
   */
  def translate(clause : AST.SimpleClause) : CCTerm = clause match {
    case ac : AST.SimpleClauseAssigns => throwNotImpl(ac)
    case ec : AST.SimpleClauseEnsures => translate(ec.ensuresclause_)
  }

  def translate(clause : AST.EnsuresClause) : CCTerm = {
    val funCtx = ctx.asInstanceOf[FunctionContext]
    inPostCond = true
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, funCtx.getPostGlobalVar(v.name).get))).toMap
    val res = translatePred(clause.asInstanceOf[AST.AnEnsuresClause].expr_)
    inPostCond = false
    res
  }

  def translate(clause : AST.RequiresClause) : CCTerm = {
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams ++ ctx.getGlobals).map(v =>
      (v.name, funCtx.getOldVar(v.name).get)).toMap
    translatePred(clause.asInstanceOf[AST.ARequiresClause].expr_)
  }

  private def reqClauseName(c : AST.RequiresClause) : Option[String] =
    namingName(c.asInstanceOf[AST.ARequiresClause].expr_)

  private def ensClauseName(c : AST.SimpleClauseEnsures) : Option[String] =
    namingName(c.ensuresclause_.asInstanceOf[AST.AnEnsuresClause].expr_)

  private def namingName(e : AST.Expr) : Option[String] = e match {
    case n : AST.ENaming1 => Some(n.id_)
    case n : AST.ENaming2 => Some(n.string_)
    case _                => None
  }

  def translate(expr : AST.Expr) : CCTerm = expr match {
    case e : AST.ENaming1  => translate(e.expr_)
    case e : AST.ENaming2  => translate(e.expr_)
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
    case e : AST.ETypeCast    => getType(e.typeexpr_).cast(translate(e.expr_))
    case e : AST.ESizeOfTerm  => ???
    case e : AST.ESizeOfType  => ???
    case e : AST.EArrayAccess => translateArrayAccessExpr(e)
    case e : AST.EStructFieldAccess =>
      translateStructFieldAccessExpr(e)
    case e : AST.EStructPtrFieldAccess =>
      translateStructPtrFieldAccessExpr(e)
    case e : AST.EArrayFunMod => ???
    case e : AST.EFieldFunMod => ???
    case e : AST.EApplication => translateApplicationExpr(e)
    case e : AST.EOld         => translateOldExpr(e)
    case e : AST.EAt          => translateAtExpr(e)
    case e : AST.EValid       => translateValidExpr(e)
    case e : AST.EValidRead   => translateValidReadExpr(e)
    case e : AST.ESeparated   => translateSeparatedExpr(e)
    case e : AST.ELit         => translateLitExpr(e.lit_)
    case e : AST.EIdent       => translateIdentExpr(e)
    case e : AST.EResult      => translateResultExpr(e)
  }

  def translateLitExpr(lit : AST.Lit) : CCTerm = {
    import IExpression._
    import ap.basetypes.IdealInt
    val srcInfo = Some(getSourceInfo(lit))
    lit match {
      case t : AST.LitTrue  => CCTerm.fromFormula(IBoolLit(true), CCBool, srcInfo)
      case t : AST.LitFalse => CCTerm.fromFormula(IBoolLit(false), CCBool, srcInfo)
      case t : AST.LitInt =>
        val s = t.unboundedinteger_
        val value = if (s.startsWith("0x") || s.startsWith("0X"))
                      IdealInt(s.substring(2), 16)
                    else IdealInt(s)
        CCTerm.fromTerm(i(value), CCInt, srcInfo)
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
  def translateRelOp(relOp : AST.ERelOp) : CCTerm = {
    val lhs : ITerm = translate(relOp.expr_1).toTerm
    val rhs : ITerm = translate(relOp.expr_2).toTerm
    val srcInfo = Some(getSourceInfo(relOp))
    CCTerm.fromFormula(relOp.relop_ match {
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
  def translateEqNeq(expr : AST.Expr) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    CCTerm.fromFormula(
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
    def binArith(l : AST.Expr, r : AST.Expr)
                (op : (ITerm, ITerm) => ITerm) : CCTerm = {
      // the result keeps the operands' unified arithmetic type, not a predicate type
      val (lhs, rhs) = CCTerm.unifyTypes(translateTerm(l), translateTerm(r))
      CCTerm.fromTerm(op(lhs.toTerm, rhs.toTerm), lhs.typ, Some(srcInfo))
    }
    expr match {
      case e : AST.EPlus  => binArith(e.expr_1, e.expr_2)(_ + _)
      case e : AST.EMinus => binArith(e.expr_1, e.expr_2)(_ - _)
      case e : AST.EMult  => binArith(e.expr_1, e.expr_2)(_ * _)
      case e : AST.EDiv   => binArith(e.expr_1, e.expr_2)(_ / _)
      case e : AST.EMod   => binArith(e.expr_1, e.expr_2)(_ % _)
      case _              =>
        throw new ACSLParseException(
          "Op is recognized, got " + (printer print expr), srcInfo)
    }
  }

  /**
   * Helper function to translate expressions into predicates.
   */
  def translatePred(expr : AST.Expr) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    val t = translate(expr)
    t match {
      case pred : CCTerm if pred.originalFormula.nonEmpty => pred
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
  def translateBinaryLogicOp(expr : AST.Expr) : CCTerm = {
    val srcInfo = Some(getSourceInfo(expr))
    expr match {
      case e : AST.EEquiv => // <==>
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCTerm.fromFormula(lhs.toFormula <=> rhs.toFormula, CCBool, srcInfo)
      case e : AST.EImplies => // ==>
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCTerm.fromFormula(lhs.toFormula ==> rhs.toFormula, CCBool, srcInfo)
      case e : AST.EOr => // ||
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCTerm.fromFormula(lhs.toFormula ||| rhs.toFormula, CCBool, srcInfo)
      case e : AST.EXOr => // ^^
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCTerm.fromFormula(lhs.toFormula </> rhs.toFormula, CCBool, srcInfo)
      case e : AST.EAnd => // &&
        val lhs = translatePred(e.expr_1)
        val rhs = translatePred(e.expr_2)
        CCTerm.fromFormula(lhs.toFormula &&& rhs.toFormula, CCBool, srcInfo)
      case _ =>
        throw new ACSLParseException(
          "Not a logical operator: " + (printer print expr), srcInfo.get)
    }
  }

  /**
   * There are four cases in the ACSL grammar:
   *   term ? term : term -> term
   *   pred ? term : term -> term
   *   term ? pred : pred -> pred
   *   pred ? pred : pred -> pred
   */
  def translateTernary(expr : AST.ETernary) : CCTerm = {
    val cond : CCTerm = translate(expr.expr_1)
    val left : CCTerm = translate(expr.expr_2)
    val right : CCTerm = translate(expr.expr_3)
    val srcInfo = Some(getSourceInfo(expr))

    (cond, left, right) match {
      case (c@CCTerm(_, _, _, _), l@CCTerm(_,lType,_, None), r@CCTerm(_,rType,_, None)) =>
        if (lType != rType) {
          // TODO: support implicit type casts.
          throw new ACSLParseException(
            s"Type mismatch in $expr: $lType vs $rType. (Implicit casts are " +
            s"currently unsupported.)", srcInfo.get)
        }
        CCTerm.fromTerm(ITermITE(cond.toFormula, left.toTerm, right.toTerm),
               lType, srcInfo)
      case (c@CCTerm(_, _, _, None), l@CCTerm(_,_,_, Some(_)), r@CCTerm(_,_,_, Some(_))) =>
        CCTerm.fromFormula(IFormulaITE(c.toFormula, l.toFormula, right.toFormula),
                  CCBool, srcInfo)
      case (c@CCTerm(_, _, _, Some(_)), l@CCTerm(_,_,_, Some(_)), r@CCTerm(_,_,_, Some(_))) =>
        CCTerm.fromFormula(IFormulaITE(c.toFormula, l.toFormula, right.toFormula),
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
//    val boundTo : CCTerm = translate(pred.term_)
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
  def translateQuantified(pred : AST.Expr) : CCTerm = {
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
    val inner : CCTerm = translatePred(bodyExpr)
    val (names, terms) : (Seq[String], Seq[CCTerm]) = namedTerms.unzip
    // FIXME: If v is shadowed, this will remove the shadowed term.
    names.map(locals.remove)

    // FIXME: Look over order of creation here.
    CCTerm.fromFormula(terms.foldLeft(inner.toFormula)((formula, term) => {
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
          (v.id_, CCTerm.fromTerm(ISortedVariable(0, ctyp.toSort), ctyp, None)) // todo: line no?
        case v: AST.VarIdentPtrDeref => throwNotImpl(v)
        case v: AST.VarIdentArray => throwNotImpl(v)
      }
    })
  }

  private def getType(typ : AST.TypeName) : CCType = typ match {
    case typ : AST.TypeNameLogic => getType(typ.logictypename_)
    case typ : AST.TypeNameC => getType(typ.ctypename_)
  }

  private def getType(typ : AST.TypeExpr) : CCType = {
    val cte = typ.asInstanceOf[AST.TypeExprC].ctypeexpr_.asInstanceOf[AST.ACTypeExpr]
    cte.cmaybeabsdec_ match {
      case _ : AST.NoAbsDec =>
        getType(cte.listcspecqual_.asScala.iterator.collect {
          case sq : AST.CSpecQualTypeSpec => sq.ctypespec_
        })
      case d => throwNotImpl(d)
    }
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
  def translateValidExpr(expr : AST.EValid) : CCTerm =
    translateValidLocations(
      expr.listlocation_.asScala.toList.map(_.asInstanceOf[AST.ALocation].tset_),
      getSourceInfo(expr))

  def translateValidReadExpr(expr : AST.EValidRead) : CCTerm = {
    tricera.Util.warn(
      "\\valid_read is treated as \\valid (read-only memory is not modeled)")
    translateValidLocations(
      expr.listlocation_.asScala.toList.map(_.asInstanceOf[AST.ALocation].tset_),
      getSourceInfo(expr))
  }

  private def translateValidLocations(tSets : List[AST.TSet],
                                      srcInfo : SourceInfo) : CCTerm = {
    val res = tSets.foldLeft(IBoolLit(true) : IFormula)((formula, tset) =>
      formula &&& validLocation(tset, srcInfo))
    CCTerm.fromFormula(res, CCBool, Some(srcInfo))
  }

  // the address of an element of an array modeled with the theory of arrays
  // is valid exactly when the index is within the declared bounds
  private def mathArrayElementBounds(expr : AST.Expr) : Option[IFormula] = {
    import ap.parser.IExpression._
    expr match {
      case e : AST.EUnary if e.unaryop_.isInstanceOf[AST.UnaryAddressOf] =>
        e.expr_ match {
          case acc : AST.EArrayAccess =>
            translateTerm(acc.expr_1).typ match {
              case arr : CCArray if arr.sizeExpr.nonEmpty =>
                val idx = translateTerm(acc.expr_2).toTerm
                Some((idx >= 0) &&& (idx < arr.sizeExpr.get.toTerm))
              case _ => None
            }
          case _ => None
        }
      case _ => None
    }
  }

  private def validLocation(tset : AST.TSet, srcInfo : SourceInfo) : IFormula =
    tset match {
      case t : AST.TSetTerm =>
        mathArrayElementBounds(t.expr_) getOrElse {
          val term = translateTerm(t.expr_)
          term.typ match {
            // FIXME: Handle CCPointer in general? (Need access to field `typ`)
            case p : CCHeapPointer =>
              import ap.parser.IExpression.{toFunApplier, toPredApplier}
              val sort : Sort = p.typ.toSort
              val heap : ITerm = ctx.getOldHeapTerm
              val valid    : IFormula = ctx.getHeap.isAlloc(heap, term.toTerm)
              val readObj  : IFunApp  = ctx.getHeap.read(heap, term.toTerm)
              val corrSort : IFormula =
                ctx.getHeap.hasUserHeapCtor(readObj, ctx.getCtor(sort))
              valid & corrSort
            case p : CCHeapArrayPointer =>
              import ap.parser.IExpression.{toFunApplier, toPredApplier}
              val ops = p.ptrOps
              val heap : ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
              val addr : ITerm = ctx.getHeap.rangeNth(ops.getRange(term.toTerm),
                                                      ops.getOffset(term.toTerm))
              val valid    : IFormula = ctx.getHeap.isAlloc(heap, addr)
              val readObj  : IFunApp  = ctx.getHeap.read(heap, addr)
              val corrSort : IFormula =
                ctx.getHeap.hasUserHeapCtor(readObj, ctx.getCtor(p.elementType.toSort))
              valid & corrSort
            case t =>
              throw new ACSLParseException(
                s"$t in \\valid not a heap pointer.", srcInfo)
          }
        }
      case t => throwNotImpl(t)
    }

  def translateSeparatedExpr(expr : AST.ESeparated) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    val tSets : List[AST.TSet] =
      expr.listlocation_.asScala.toList.map(_.asInstanceOf[AST.ALocation].tset_)
    val terms : List[CCTerm] = tSets.collect({
      case t : AST.TSetTerm  => translateTerm(t.expr_)
      case t => throwNotImpl(t)
    })
    val res : IFormula =
      terms.toSeq.combinations(2).foldLeft(IBoolLit(true) : IFormula) {
        case (formula, Seq(a, b)) => formula &&& (a.toTerm =/= b.toTerm)
        case (formula, _)         => formula
      }
    CCTerm.fromFormula(res, CCBool, Some(srcInfo))
  }

  def translateIdentExpr(t : AST.EIdent) : CCTerm = {
    val srcInfo = getSourceInfo(t)
    val ident = t.id_
    // TODO: Lookup if var exists as as local binding.
    // FIXME: Order of lookups (priority)?

    val maybeTerm = ctx match {
      case stmCtx : StatementAnnotationContext =>
        stmCtx.getTermInScope(ident)
      case _ => None
    }

    maybeTerm match {
      case Some(t) => t
      case None =>
        val bound: Option[CCTerm] = locals.get(ident)
        val scoped: Option[CCTerm] =
          vars.get(ident).map(v => CCTerm.fromTerm(v.term, v.typ, v.srcInfo))
        bound.orElse(scoped).orElse(ctx.enumeratorDefs.get(ident))
          .orElse(ctx.acslPredicateDefs.get(ident).map(_ =>
            inlinePredicate(ident, Nil, srcInfo)))
          .getOrElse(
            throw new ACSLParseException(
              s"Identifier $ident not found in scope.", srcInfo))
    }
  }

  def translateUnary(expr : AST.EUnary) : CCTerm = {
    // FIXME: Probably needs type conversions.
    val srcInfo = getSourceInfo(expr)
    expr.unaryop_ match {
      case _ : AST.UnaryPlus =>
        translateTerm(expr.expr_)
      case _ : AST.UnaryMinus           =>
        val t = translateTerm(expr.expr_)
        CCTerm.fromTerm(- t.toTerm, t.typ, t.srcInfo)
      case _ : AST.UnaryNegation =>
        translate(expr.expr_) match {
          case term : CCTerm if term.originalFormula.isEmpty =>
            CCTerm.fromTerm(- term.toTerm, term.typ, term.srcInfo)
          case pred : CCTerm =>
            CCTerm.fromFormula(!pred.toFormula, pred.typ, pred.srcInfo)
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
            CCTerm.fromTerm(getObj(readObj), p.typ, t.srcInfo)
          case p => throwNotImpl(p) // FIXME: Handle stackptr
        }
      case _ : AST.UnaryAddressOf =>
        expr.expr_ match {
          case arrAcc : AST.EArrayAccess => translateAddressOfArrayElement(arrAcc)
          case other                     => throwNotImpl(other)
        }
    }
  }

  def translateAddressOfArrayElement(term : AST.EArrayAccess) : CCTerm = {
    val srcInfo = getSourceInfo(term)
    val array = translateTerm(term.expr_1)
    val index = translateTerm(term.expr_2)
    array.typ match {
      case p : CCHeapArrayPointer =>
        val ops = p.ptrOps
        val elemPtr = ops.mkArrayPtr(ops.getRange(array.toTerm),
                                     ops.getOffset(array.toTerm) + index.toTerm)
        CCTerm.fromTerm(elemPtr, p, array.srcInfo)
      case _ =>
        throw new ACSLParseException(
          s"Cannot take address of $array[$index].", srcInfo)
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
        val access: IFunApp = ctx.getHeap.rangeNth(array.toTerm, index.toTerm)
        val readObj: IFunApp = ctx.getHeap.read(heap, access)
        val getObj: IFunction = ctx.sortGetter(p.typ.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].", srcInfo)
        )
        CCTerm.fromTerm(getObj(readObj), p.typ, array.srcInfo)
      case p : CCHeapArrayPointer =>
        val heap: ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
        val ops = p.ptrOps
        val rawRange = ops.getRange(array.toTerm)
        val effectiveIndex = ops.getOffset(array.toTerm) + index.toTerm
        val access: IFunApp = ctx.getHeap.rangeNth(rawRange, effectiveIndex)
        val readObj: IFunApp = ctx.getHeap.read(heap, access)
        val getObj: IFunction = ctx.sortGetter(p.elementType.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].", srcInfo)
        )
        CCTerm.fromTerm(getObj(readObj), p.elementType, array.srcInfo)
      case p : CCArray => // todo: currently does not use wrappers, should match the encoding in CCReader
        val readObj: IFunApp = p.arrayTheory.select(array.toTerm, index.toTerm)
        val getObj: IFunction = ctx.sortGetter(p.elementType.toSort).getOrElse(
          throw new ACSLParseException(s"Cannot access $array[$index].", srcInfo)
        )
        //CCTerm.fromTerm(getObj(readObj), p.elementType, array.srcInfo)
        CCTerm.fromTerm(readObj, p.elementType, array.srcInfo)
      case _ =>
        throw new ACSLParseException("Array access could not be handled.", srcInfo)
    }
  }

  def translateStructFieldAccessExpr(expr: AST.EStructFieldAccess) : CCTerm =
    getField(translate(expr.expr_), expr.id_,
                 printer.print(expr), getSourceInfo(expr))

  def translateStructPtrFieldAccessExpr(expr : AST.EStructPtrFieldAccess)
  : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    val ptr     = translate(expr.expr_)
    ptr.typ match {
      case p : CCHeapPointer =>
        val heap    = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
        val readObj = IFunApp(ctx.getHeap.read, Seq(heap, ptr.toTerm))
        val getObj  = ctx.sortGetter(p.typ.toSort).getOrElse(
          throw new ACSLParseException(
            s"Cannot dereference ${printer.print(expr)}.", srcInfo))
        val structTerm =
          CCTerm.fromTerm(IFunApp(getObj, Seq(readObj)), p.typ, Some(srcInfo))
        getField(structTerm, expr.id_, printer.print(expr), srcInfo)
      case _ =>
        throw new ACSLParseException(
          s"Tried to access ${printer.print(expr)} but $ptr is not a pointer.",
          srcInfo)
    }
  }

  private def getField(structTerm : CCTerm, fieldName : String,
                           shown : String, srcInfo : SourceInfo) : CCTerm = {
    val struct = structTerm.typ match {
      case s : CCStruct      => s
      case f : CCStructField => f.structs(f.structName)
      case _ =>
        throw new ACSLParseException(
          s"Tried to access $shown but $structTerm is not a struct.", srcInfo)
    }
    struct.getFieldIndex(fieldName) match {
      case -1 =>
        throw new ACSLParseException(
          s"$fieldName is not a field of $struct: $shown", srcInfo)
      case fieldInd =>
        val fieldSelector = struct.getADTSelector(fieldInd)
        val fieldTyp = struct.getFieldType(fieldInd)
        CCTerm.fromTerm(IFunApp(fieldSelector, Seq(structTerm.toTerm)),
               fieldTyp, Some(srcInfo))
    }
  }

  private def translateInOldState(e : AST.Expr) : CCTerm = {
    val old = vars
    val funCtx = ctx.asInstanceOf[FunctionContext]
    vars = (funCtx.getParams.map(v => (v.name, funCtx.getOldVar(v.name).get))
        ++ funCtx.getGlobals.map(v => (v.name, funCtx.getOldVar(v.name).get))).toMap
    useOldHeap = true
    val res = translateTerm(e)
    useOldHeap = false
    vars = old
    res
  }

  def translateOldExpr(expr : AST.EOld) : CCTerm =
    if (ctx.isInstanceOf[FunctionContext]) translateInOldState(expr.expr_)
    else throw new ACSLParseException(
      "\\old is not visible in a statement annotation; use \\at(e, Pre)",
      getSourceInfo(expr))

  // ACSL 2.4.3 Table 2.1: Old/Post are contract-only. In a statement annotation
  // Pre and C-labels are handled by the capture mechanism (CCReader rewrites them
  // before this runs), so reaching a C-label here means it was not captured (e.g.
  // used before the label, in an exited block, or undefined).
  private def labelUnavailableMsg(label : Label, id : String) : String = {
    val where =
      if (ctx.isInstanceOf[StatementAnnotationContext]) "a statement annotation"
      else "this contract clause"
    label match {
      case Label.Old | Label.Post => s"label '$id' is not visible in $where (ACSL 2.4.3)"
      case Label.CLabel(_)        => s"C-label '$id' is not visible at this use in $where"
      case _                      => s"label '$id' is not yet supported in $where"
    }
  }

  def translateAtExpr(expr : AST.EAt) : CCTerm = {
    val labelId = labelBindings.getOrElse(expr.id_, expr.id_)
    Label(labelId) match {
      case Label.Pre | Label.Old if ctx.isInstanceOf[FunctionContext] =>
        translateInOldState(expr.expr_)
      case Label.Here               => translateTerm(expr.expr_)
      case Label.Post if inPostCond => translateTerm(expr.expr_)
      case label => throw new ACSLParseException(
        labelUnavailableMsg(label, labelId), getSourceInfo(expr))
    }
  }

  def translateApplicationExpr(expr : AST.EApplication) : CCTerm =
    inlinePredicate(expr.id_, expr.listexpr_.asScala.toList, getSourceInfo(expr))

  private def inlinePredicate(name     : String,
                              argExprs : List[AST.Expr],
                              srcInfo  : SourceInfo) : CCTerm = {
    val pdef = ctx.acslPredicateDefs.getOrElse(name,
      throw new ACSLParseException(s"Unknown ACSL predicate '$name'.", srcInfo))
    if (inliningStack contains name)
      throw new ACSLParseException(
        s"Recursive ACSL predicate '$name' cannot be inlined.", srcInfo)
    if (argExprs.size != pdef.valueParams.size)
      throw new ACSLParseException(
        s"ACSL predicate '$name' expects ${pdef.valueParams.size} argument(s)" +
        s" but got ${argExprs.size}.", srcInfo)

    val argTerms    = argExprs.map(translateTerm)
    val savedLocals = pdef.valueParams.map(p => (p, locals.get(p)))
    val savedLabels = pdef.labelParams.map(l => (l, labelBindings.get(l)))
    pdef.valueParams.zip(argTerms).foreach { case (p, a) => locals.put(p, a) }
    pdef.labelParams.foreach(l => labelBindings.put(l, "Here"))
    inliningStack = name :: inliningStack
    try translate(pdef.body)
    finally {
      inliningStack = inliningStack.tail
      savedLocals.foreach {
        case (p, Some(t)) => locals.put(p, t)
        case (p, None)    => locals.remove(p)
      }
      savedLabels.foreach {
        case (l, Some(s)) => labelBindings.put(l, s)
        case (l, None)    => labelBindings.remove(l)
      }
    }
  }

  def translateResultExpr(expr : AST.EResult) : CCTerm = {
    val srcInfo = getSourceInfo(expr)
    if (!ctx.isInstanceOf[FunctionContext])
      throw new ACSLParseException(
        "\\result is not visible in a statement annotation", srcInfo)
    val funCtx = ctx.asInstanceOf[FunctionContext]
    if (!inPostCond) {
      throw new ACSLParseException("\\result has no meaning.", srcInfo)
    }

    funCtx.getResultVar.map(v => CCTerm.fromTerm(v.term, v.typ, v.srcInfo))
      .getOrElse(
        throw new ACSLParseException("\\result used in void function.", srcInfo)
      )
  }

  private def throwNotImpl[T](obj : T) = {
    throw new NotImplementedError(s"ACSL support missing for ${obj.getClass}.")
  }
}
