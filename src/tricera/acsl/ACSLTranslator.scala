package tricera.acsl

import tricera.acsl._
import tricera.acsl.{Absyn => AST};

import collection.JavaConverters._

import ap.parser.IExpression
import ap.parser.{ISortedQuantified, IConstant, ITerm, IIntLit, IBoolLit,
                  IFunApp, IFunction, IFormula, IFormulaITE, IVariable, ISortedVariable}
import ap.types.{MonoSortedPredicate, SortedConstantTerm, Sort}
import ap.theories.{Heap}

import tricera.concurrency.CCReader.{CCType, CCVar, CCTerm, CCExpr}
import tricera.concurrency.CCReader

class ACSLParseException(msg : String) extends Exception(msg)
class ACSLTranslateException(msg : String) extends Exception(msg)

object ACSLTranslator {

  trait Context {
    def getOldVar(ident : String) : Option[CCVar]
    def getParams  : Seq[CCVar]
    def getGlobals : Seq[CCVar]
    def getResultVar : Option[CCVar]
    def isHeapEnabled : Boolean
    def getHeap : Heap
    def getHeapTerm : ITerm
    def getOldHeapTerm : ITerm
    def sortWrapper(s : Sort) : Option[IFunction]
    def sortGetter(s : Sort) : Option[IFunction]
    def getCtor(s : Sort) : Int
    def getTypOfPointer(t : CCType) : CCType

    implicit val arithMode : CCReader.ArithmeticMode.Value
  }

  def translateContract(annot : String, ctx : Context) : FunctionContract = {
    val l : Yylex = new Yylex(new java.io.StringReader(preprocess(annot)))
    val p : parser = new parser(l, l.getSymbolFactory())
    try {
      val ast : AST.Annotation = p.pAnnotation()
      val translator = new ACSLTranslator(ast, ctx)

      // FIXME: Probably handle this in companion class aswell.
      ast match {
        case ac : AST.AnnotContract => translator.translate(ac.functioncontract_)
        case _ => throw new ACSLParseException("Not a contract annotation.")
      }
    } catch {
      // FIXME: Exceptions not thrown by lexer/parser should just be re-thrown?
      case CCReader.NeedsHeapModelException => throw CCReader.NeedsHeapModelException
      case e : Exception =>
        throw new ACSLParseException(
          "At line " + String.valueOf(l.line_num()) +
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

class ACSLTranslator(annot : AST.Annotation, ctx : ACSLTranslator.Context) {
  import scala.collection.mutable.{HashMap => MHashMap}
  import scala.collection.immutable.Map
  import ctx.arithMode
  val locals = new MHashMap[String, CCTerm]
  var vars : Map[String, CCVar] = Map()
  // NOTE: Might want a "state" covering various state, if more use cases.
  //       Currently only used for `\result` construct.
  // Use DynamicVariable?
  var inPostCond = false
  var useOldHeap = false

  // TODO: Use annot from field and a generic translate method.

  // TODO: Make all `translate` private?
  // ---- Contracts ------------------------------------------
  def translate(contract : AST.FunctionContract) : FunctionContract = contract match {
    case c : AST.Contract =>
      val rcs = c.listrequiresclause_.asScala.toList
      val scs = c.listsimpleclause_.asScala.toList

      val nils : (List[AST.SimpleClauseEnsures], List[AST.SimpleClauseAssigns]) = (Nil, Nil)
      val (ecs : List[AST.SimpleClauseEnsures], acs : List[AST.SimpleClauseAssigns]) =
        scs.foldRight(nils) {
          case (ec : AST.SimpleClauseEnsures, (ecs, acs)) => (ec :: ecs, acs)
          case (ac : AST.SimpleClauseAssigns, (ecs, acs)) => (ecs, ac :: acs)
          case _ => throw new ACSLParseException("Unsupported simple clause.")
        }
 
      // NOTE: `pre` and `post` defaults to true given usage of `and`.
      val pre  : IFormula = IExpression.and(rcs.map(translate))
      val post : IFormula = IExpression.and(ecs.map(translate))

      val assigns : (IFormula, IFormula) = acs match {
        case Nil => (IBoolLit(true), IBoolLit(true))
        case acs =>
          val (idents, ptrDerefs) : (Set[CCTerm], Set[CCTerm]) = 
            acs.foldLeft(Set[CCTerm](), Set[CCTerm]()) ({(sets, clause) =>
            val (i, p) = 
              translateAssigns(clause.assignsclause_.asInstanceOf[AST.AnAssignsClause])
            (i.union(sets._1), p.union(sets._2))
            }
          )

          val globConstraint : IFormula = 
            if (idents.isEmpty) {
              ctx.getGlobals.foldLeft(IBoolLit(true) : IFormula) (
                (formula, globVar) => {
                  val glob    : ITerm = globVar.term
                  val globOld : ITerm = ctx.getOldVar(globVar.name).get.term
                  formula &&& glob === globOld
                }
              )
            } else {
              val globals : Seq[ITerm] = ctx.getGlobals.map(_.term)
              val oldGlobals : Seq[ITerm] = 
                ctx.getGlobals.map(g => ctx.getOldVar(g.name).get.term)
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
                if (ctx.isHeapEnabled) {
                  val sameHeap = ctx.getHeapTerm === ctx.getOldHeapTerm
                  (sameHeap, sameHeap)
                } else {
                  (IBoolLit(true), IBoolLit(true))
                }
            } else {
                val ptrs = ptrDerefs.map(_.toTerm)

                import ap.parser.IExpression.toFunApplier
                val heap : Heap = ctx.getHeap
                val newHeap : ITerm = ctx.getHeapTerm
                val oldHeap : ITerm = ctx.getOldHeapTerm

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

                val assumeConstr : IFormula = newHeap === modifiedHeap

                // Implicit universal
                val quantified : ITerm = new SortedConstantTerm("_p", ctx.getHeap.AddressSort)
                val quantifiedNotEqual : IFormula =
                  ptrs.foldLeft(IBoolLit(true) : IFormula) (
                    (formula, ptr) => formula &&& quantified =/= ptr
                  )

                val readEq : IFormula = 
                  heap.read(newHeap, quantified) === heap.read(oldHeap, quantified)
                val assertConstr : IFormula = quantifiedNotEqual ==> readEq

                (assertConstr, assumeConstr)
            }
          (heapAssert &&& globConstraint, heapAssume &&& globConstraint)
      }

      new FunctionContract(pre, post, assigns._1, assigns._2)

    case _ => throwNotImpl(contract)
  }

  def translateAssigns(clause : AST.AnAssignsClause) : (Set[CCTerm], Set[CCTerm]) = {
    vars = (ctx.getParams.map(v => (v.name, ctx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, v))).toMap
    clause.locations_ match {
      case ls : AST.LocationsSome    =>
        val tSets : List[AST.TSet] = 
          ls.listlocation_.asScala.toList.map(_.asInstanceOf[AST.ALocation].tset_)
        val nils = (Nil : List[CCTerm], Nil : List[CCTerm])
        val terms : (List[CCTerm], List[CCTerm]) = tSets.foldRight(nils) ({
          case (t : AST.TSetTerm, (idents, ptrDerefs)) => 
            t.term_ match {
              case i : AST.TermIdent => (translate(i) :: idents, ptrDerefs)
              case p : AST.TermUnaryOp if p.unaryop_.isInstanceOf[AST.UnaryOpPtrDeref] => {
                (idents, translate(p.term_) :: ptrDerefs)
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
  def translate(clause : AST.SimpleClause) : IFormula = clause match {
    case ac : AST.SimpleClauseAssigns => throwNotImpl(ac)
    case ec : AST.SimpleClauseEnsures => translate(ec.ensuresclause_)
  }

  
  def translate(clause : AST.EnsuresClause) : IFormula = {
    inPostCond = true
    vars = (ctx.getParams.map(v => (v.name, ctx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, v))).toMap
    val res = translate(clause.asInstanceOf[AST.AnEnsuresClause].predicate_)
    inPostCond = false
    res
  }

  def translate(clause : AST.RequiresClause) : IFormula = {
    vars = (ctx.getParams.map(v => (v.name, v))
        ++ ctx.getGlobals.map(v => (v.name, v))).toMap
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
    case p : AST.PredExists           => throwNotImpl(p)
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
    right.unary_!
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
    val boundTo : CCTerm  = translate(pred.term_)

    locals.put(ident, boundTo)
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

  def translate(pred : AST.PredForAll) : IFormula = {
    val binders : Seq[AST.ABinder] = 
      pred.listbinder_.asScala.toList.map(_.asInstanceOf[AST.ABinder])
    val namedTerms : Seq[(String, CCTerm)] = bindersToConstants(binders)

    namedTerms.map(t => locals.put(t._1, t._2))
    val inner : IFormula = translate(pred.predicate_)
    val (names, terms) : (Seq[String], Seq[CCTerm]) = namedTerms.unzip
    // FIXME: If v is shadowed, this will remove the shadowed term.
    names.map(locals.remove(_))

    // FIXME: Look over order of creation here.
    // FIXME: Use IExpression.all?
    terms.foldLeft(inner)((formula, term) =>
        new ISortedQuantified(IExpression.Quantifier.ALL, term.typ.toSort, formula)
    )
  }

  private def bindersToConstants(binders : Seq[AST.ABinder]) : Seq[(String, CCTerm)] = {
    binders.flatMap(b => {
      val typ : AST.CTypeSpecifier = b.typename_.asInstanceOf[AST.TypeNameC].ctypespecifier_
      val ctyp : CCType = toCCType(typ)
      val idents : Seq[AST.VariableIdent] = b.listvariableident_.asScala.toList
      idents.map(i => i match {
        case v : AST.VariableIdentId =>
          (v.id_, CCTerm(ISortedVariable(0, ctyp.toSort), ctyp, None)) // todo: line no?
        case v : AST.VariableIdentPtrDeref    => throwNotImpl(v)
        case v : AST.VariableIdentArray       => throwNotImpl(v)
        case v : AST.VariableIdentParentheses => throwNotImpl(v)
      })
    })
  }

  private def toCCType(typ : AST.CTypeSpecifier) : CCType = typ match {
    case t : AST.CTypeSpecifierVoid     => throwNotImpl(t)
    case t : AST.CTypeSpecifierChar     => throwNotImpl(t)
    case t : AST.CTypeSpecifierShort    => throwNotImpl(t)
    case t : AST.CTypeSpecifierInt      => CCReader.CCInt()
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

  def translate(pred : AST.PredValid) : IFormula = {
    val tSets : List[AST.TSet] = 
      pred.listlocation_.asScala.toList.map(_.asInstanceOf[AST.ALocation].tset_)
    val terms : List[CCTerm] = tSets.collect({
      case t : AST.TSetTerm  => translate(t.term_)
      case t => throwNotImpl(t)
    })

    // FIXME: Typecheck terms?
    terms.foldLeft(IBoolLit(true) : IFormula)((formula, term) =>
      term.typ match {
        // FIXME: Handle CCPointer in general? (Need access to field `typ`)
        case p : CCReader.CCHeapPointer => 
          import ap.parser.IExpression.{toFunApplier, toPredApplier}
          val sort : Sort = p.typ.toSort
          val heap : ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
          val valid    : IFormula = ctx.getHeap.isAlloc(heap, term.toTerm)
          val readObj  : IFunApp  = ctx.getHeap.read(heap, term.toTerm)
          val corrSort : IFormula = ctx.getHeap.heapADTs.hasCtor(readObj, ctx.getCtor(sort))
          formula &&& valid & corrSort
        case t =>
          throw new ACSLParseException(s"$t in \\valid not a heap pointer.")
      }
    )
  }

  // ---- Terms ----------------------------------------------
  def translate(term : AST.Term) : CCTerm = term match {
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
    val bound  : Option[CCTerm] = locals.get(ident)
    val scoped : Option[CCTerm] = vars.get(ident).map(v => CCTerm(v.term, v.typ, v.srcInfo))
    bound.getOrElse(
      scoped.getOrElse(
        throw new ACSLParseException(s"Identifier $ident not found in scope.")
      )
    )
  }

  def translate(term : AST.TermUnaryOp) : CCTerm = {
    val right : CCTerm = translate(term.term_)
    term.unaryop_ match {
      case op : AST.UnaryOpPlus            => throwNotImpl(op)
      case op : AST.UnaryOpMinus           => throwNotImpl(op) // right.unary_-
      case op : AST.UnaryOpNegation => 
        CCTerm(right.toTerm.unary_-, right.typ, right.srcInfo)
      case op : AST.UnaryOpComplementation => throwNotImpl(op)
      case op : AST.UnaryOpPtrDeref => 
        right.typ match {
          case p : CCReader.CCHeapPointer => 
            import ap.parser.IExpression.toFunApplier
            val heap : ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
            val readObj : IFunApp = ctx.getHeap.read(heap, right.toTerm)
            val getObj  : IFunction = ctx.sortGetter(p.typ.toSort).getOrElse(
                throw new ACSLParseException(s"Cannot dereference pointer of type ${p.typ}.")
              )
            CCTerm(getObj(readObj), p.typ, right.srcInfo)
          // FIXME: Handle stackptr
          case p => throwNotImpl(p)
        }
      case op : AST.UnaryOpAddressOf => throwNotImpl(op)
        //IFunApp(ctx.getHeap.nthAddr, Seq(ctx.getHeapTerm, right))
    }
  }

  def translate(term : AST.TermBinOp) : CCTerm = {
    val left  : CCTerm = translate(term.term_1)
    val right : CCTerm = translate(term.term_2)
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
        import ap.theories.nia.GroebnerMultiplication.mult
        CCTerm(mult(left.toTerm, right.toTerm), typ, srcInfo)
      case op : AST.BinOpDiv =>
        import ap.theories.nia.GroebnerMultiplication.tDiv
        CCTerm(tDiv(left.toTerm, right.toTerm), typ, srcInfo)
      case op : AST.BinOpMod =>
        import ap.theories.nia.GroebnerMultiplication.tMod
        CCTerm(tMod(left.toTerm, right.toTerm), typ, srcInfo)
      // FIXME: Comparisons create IFormula:s.. Desired?
      case op : AST.BinOpEQ           => throwNotImpl(op) // left === right
      case op : AST.BinOpNEQ          => throwNotImpl(op) // left =/= right
      case op : AST.BinOpLEQ          => throwNotImpl(op) // left <= right
      case op : AST.BinOpGEQ          => throwNotImpl(op) // left >= right
      case op : AST.BinOpGT           => throwNotImpl(op) // left > right
      case op : AST.BinOpLT           => throwNotImpl(op) // left < right
      case op : AST.BinOpAnd          => throwNotImpl(op)
      case op : AST.BinOpOr           => throwNotImpl(op)
      case op : AST.BinOpXOr          => throwNotImpl(op)
      case op : AST.BinOpLShift       => throwNotImpl(op)
      case op : AST.BinOpRShift       => throwNotImpl(op)
      case op : AST.BinOpBitwiseAnd   => throwNotImpl(op)
      case op : AST.BinOpBitwiseOr    => throwNotImpl(op)
      case op : AST.BinOpBitwiseImpl  => throwNotImpl(op)
      case op : AST.BinOpBitwiseEquiv => throwNotImpl(op)
      case op : AST.BinOpBitwiseXOr   => throwNotImpl(op)
    }
  }

  def translate(term : AST.TermArrayAccess) : CCTerm = {
    // TODO: Unsure if working.
    val array : CCTerm = translate(term.term_1)
    val index : CCTerm = translate(term.term_2)

    val typ : CCType = array.typ match {
      case p : CCReader.CCHeapPointer => p.typ
      case _ => 
        throw new ACSLParseException("Array access not on heap pointer.")
    }

    import ap.parser.IExpression.toFunApplier
    val heap : ITerm = if (useOldHeap) ctx.getOldHeapTerm else ctx.getHeapTerm
    val access  : IFunApp = ctx.getHeap.nth(array.toTerm, index.toTerm)
    val readObj : IFunApp = ctx.getHeap.read(heap, access)
    val getObj  : IFunction = ctx.sortGetter(typ.toSort).getOrElse(
      throw new ACSLParseException(s"Cannot access $array[$index].")
    )
    CCTerm(getObj(readObj), typ, array.srcInfo)
  }

  def translate(term : AST.TermParentheses) : CCTerm = {
    translate(term.term_)
  }

  def translate(term : AST.TermOld) : CCTerm = {
    val old = vars
    vars = (ctx.getParams.map(v => (v.name, ctx.getOldVar(v.name).get))
        ++ ctx.getGlobals.map(v => (v.name, ctx.getOldVar(v.name).get))).toMap
    useOldHeap = true
    val res = translate(term.term_)
    useOldHeap = false
    vars = old
    res
  }

  def translate(term : AST.TermResult) : CCTerm = {
    if (!inPostCond) {
      throw new ACSLParseException("\\result has no meaning.")
    }

    ctx.getResultVar.map(v => CCTerm(v.term, v.typ, v.srcInfo))
      .getOrElse(throw new ACSLParseException("\\result used in void function."))
  }

  // ---- Literals -------------------------------------------
  def translate(literal : AST.Literal) : CCTerm = literal match {
    // Do we want to use CCTypes here or what?
    case l : AST.LiteralTrue   => throwNotImpl(l) // IBoolLit(true)
    case l : AST.LiteralFalse  => throwNotImpl(l) // IBoolLit(false)
    case l : AST.LiteralInt    => 
      CCTerm(IExpression.i(l.integer_), CCReader.CCInt(), None) // todo; line no?
    case l : AST.LiteralReal   => throwNotImpl(l)
    case l : AST.LiteralString => throwNotImpl(l) // ap.theories.string.StringTheory?
    case l : AST.LiteralChar   => throwNotImpl(l)
  }

  private def throwNotImpl[T](obj : T) = {
    throw new NotImplementedError(s"Support missing for ${obj.getClass}.")
  }
}
