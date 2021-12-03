package tricera.acsl

import tricera.acsl._
import tricera.acsl.{Absyn => AST};

import collection.JavaConverters._

import ap.parser.IExpression
import ap.parser.{ISortedQuantified, IConstant, ITerm, IIntLit, IBoolLit, IFormula, IFormulaITE}
import ap.types.{SortedConstantTerm, Sort}

import tricera.concurrency.CCReader
import tricera.concurrency.CCReader.{CCType, CCExpr}

class ACSLParseException(msg : String) extends Exception(msg)
class ACSLTranslateException(msg : String) extends Exception(msg)

object ACSLTranslator {

  trait Context {
    // Lookup if a variable referenced in annotation exists (in scope).
    // For function contract scope is _atleast_ global vars + formal args.
    def lookupVar(ident : String) : Option[CCReader#CCVar]

    def toSort(typ : CCType) : Sort

    // Eventually we will need lookup for globally defined ACSL logic
    // functions/predicate reference (if/when that gets supported) like:
    // def lookupGlobalPredicate(ident : String) : Option[acsl.GlobalPredicate]
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
  val locals = new MHashMap[String, ITerm]

  // TODO: Use annot from field and a generic translate method.

  // TODO: Make all `translate` private?
  // ---- Contracts ------------------------------------------
  def translate(contract : AST.FunctionContract) : FunctionContract = contract match {
    case c : AST.Contract =>
      val requiresClauses = c.listrequiresclause_.asScala.toList
      val simpleClauses = c.listsimpleclause_.asScala.toList
      val (ensuresClauses, assignsClauses) = simpleClauses.partition(sc => {
        sc.isInstanceOf[AST.SimpleClauseEnsures]
      })
      
      // NOTE: `pre` and `post` defaults to true given usage of `and`.
      val pre = IExpression.and(requiresClauses.map(translate))
      // TODO: val assigns = ???
      val post = IExpression.and(ensuresClauses.map(translate))
      new FunctionContract(pre,/* assigns, */post)

    case _ => throwNotImpl(contract)
  }

  def translate(clause : AST.SimpleClause) : IFormula = clause match {
    case ac : AST.SimpleClauseAssigns => throwNotImpl(ac)
    case ec : AST.SimpleClauseEnsures => translate(ec.ensuresclause_)
  }

  
  def translate(clause : AST.EnsuresClause) : IFormula = {
    translate(clause.asInstanceOf[AST.AnEnsuresClause].predicate_)
  }

  def translate(clause : AST.RequiresClause) : IFormula = clause match {
    case c : AST.ARequiresClause => translate(c.predicate_) 
    case _ => throwNotImpl(clause) // NOTE: Shouldn't happen? Assert instead?
  }

  // ---- Predicates -----------------------------------------
  def translate(pred : AST.Predicate) : IFormula = pred match {
    case p : AST.PredTrue             => translate(p)
    case p : AST.PredFalse            => translate(p)
    case p : AST.PredRelOp            => translate(p)
    case p : AST.PredApplication      => throwNotImpl(p)
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
    case p : AST.PredicateOld         => throwNotImpl(p)
  }

  def translate(pred : AST.PredTrue) : IFormula = {
    IBoolLit(true)
  }

  def translate(pred : AST.PredFalse) : IFormula = {
    IBoolLit(false)
  }

  def translate(pred : AST.PredRelOp) : IFormula = {
    val left  : ITerm = translate(pred.term_1)
    val right : ITerm = translate(pred.term_2)
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
    val boundTo : ITerm  = translate(pred.term_)

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
    val terms : Seq[SortedConstantTerm] = bindersToConstants(binders)

    terms.map(v => locals.put(v.name, v))
    val inner : IFormula = translate(pred.predicate_)
    terms.map(v => locals.remove(v.name))
    
    // FIXME: Look over order of creation here.
    // FIXME: Use IExpression.all?
    terms.foldLeft(inner)((formula, term) =>
        new ISortedQuantified(IExpression.Quantifier.ALL, term.sort, formula)
    )
  }

  private def bindersToConstants(binders : Seq[AST.ABinder]) : Seq[SortedConstantTerm] = {
    binders.flatMap(b => {
      val typ : AST.CTypeSpecifier = b.typename_.asInstanceOf[AST.TypeNameC].ctypespecifier_
      val ctyp : CCType = toCCType(typ)
      val idents : Seq[AST.VariableIdent] = b.listvariableident_.asScala.toList
      idents.map(i => i match {
        case v : AST.VariableIdentId => new SortedConstantTerm(v.id_, ctx.toSort(ctyp))
        case v : AST.VariableIdentPtrDeref    => throwNotImpl(v)
        case v : AST.VariableIdentArray       => throwNotImpl(v)
        case v : AST.VariableIdentParentheses => throwNotImpl(v)
      })
    })
  }

  private def toCCType(typ : AST.CTypeSpecifier) : CCType = typ match {
    case t : AST.CTypeSpecifierVoid => throwNotImpl(t)
    case t : AST.CTypeSpecifierChar => throwNotImpl(t)
    case t : AST.CTypeSpecifierShort => throwNotImpl(t)
    case t : AST.CTypeSpecifierInt => CCReader.CCInt
    case t : AST.CTypeSpecifierLong => throwNotImpl(t)
    case t : AST.CTypeSpecifierFloat => throwNotImpl(t)
    case t : AST.CTypeSpecifierDouble => throwNotImpl(t)
    case t : AST.CTypeSpecifierSigned => throwNotImpl(t)
    case t : AST.CTypeSpecifierUnsigned => throwNotImpl(t)
    //CTypeSpecifierStruct.   CTypeSpecifier ::= "struct" Id ;
    //CTypeSpecifierUnion.    CTypeSpecifier ::= "union" Id ;
    //CTypeSpecifierEnum.     CTypeSpecifier ::= "enum" Id ;
    //CTypeSpecifierId.       CTypeSpecifier ::= Id ;
  }

  // `INamedPart` relevant?
  def translate(pred : AST.PredSyntacticNaming) : IFormula = {
    translate(pred.predicate_)
  }

  def translate(pred : AST.PredSyntacticNaming2) : IFormula = {
    translate(pred.predicate_)
  }

  // ---- Terms ----------------------------------------------
  def translate(term : AST.Term) : ITerm = term match {
    case t : AST.TermLiteral                 => translate(t)
    case t : AST.TermIdent                   => translate(t)
    case t : AST.TermUnaryOp                 => translate(t)
    case t : AST.TermBinOp                   => translate(t)
    case t : AST.TermArrayAccess             => throwNotImpl(t)
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
    case t : AST.TermOld                     => throwNotImpl(t)
    case t : AST.TermResult                  => throwNotImpl(t)
  }

  def translate(term : AST.TermLiteral) : ITerm = {
    translate(term.literal_)
  }

  def translate(term : AST.TermIdent) : ITerm = {
    val ident = term.id_
    // TODO: Lookup if var exists as as local binding.
    // FIXME: Order of lookups (priority)?
    val bound  : Option[ITerm] = locals.get(ident)
    val scoped : Option[ITerm] = ctx.lookupVar(ident).map(_.term)
    bound.getOrElse(
      scoped.getOrElse(
        throw new ACSLParseException(s"Identifier $ident not found in scope.")
      )
    )
  }

  def translate(term : AST.TermUnaryOp) : ITerm = {
    val right : ITerm = translate(term.term_)
    term.unaryop_ match {
      case op : AST.UnaryOpPlus            => throwNotImpl(op)
      case op : AST.UnaryOpMinus           => throwNotImpl(op)
      case op : AST.UnaryOpNegation        => right.unary_-
      case op : AST.UnaryOpComplementation => throwNotImpl(op)
      case op : AST.UnaryOpPtrDeref        => throwNotImpl(op)
      case op : AST.UnaryOpAddressOf       => throwNotImpl(op)
    }
  }

  def translate(term : AST.TermBinOp) : ITerm = {
    val left  : ITerm = translate(term.term_1)
    val right : ITerm = translate(term.term_2)
    term.binop_ match {
      case op : AST.BinOpPlus         => left + right
      case op : AST.BinOpMinus        => left - right
      case op : AST.BinOpMult         => left * right
      case op : AST.BinOpDiv          => throwNotImpl(op)
      case op : AST.BinOpMod          => throwNotImpl(op)
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

  def translate(term : AST.TermParentheses) : ITerm = {
    translate(term.term_)
  }

  // ---- Literals -------------------------------------------
  def translate(literal : AST.Literal) : ITerm = literal match {
    // Do we want to use CCTypes here or what?
    case l : AST.LiteralTrue   => throwNotImpl(l)
    case l : AST.LiteralFalse  => throwNotImpl(l)
    case l : AST.LiteralInt    => translate(l)
    case l : AST.LiteralReal   => throwNotImpl(l)
    case l : AST.LiteralString => throwNotImpl(l)
    case l : AST.LiteralChar   => throwNotImpl(l)
  }

  def translate(li : AST.LiteralInt) : ITerm = {
    // FIXME: Unsure if this is semantically correct with integer types and all.
    //        Probably need to know ArithmeticMode as context.
    IExpression.i(li.integer_)
  }

  private def throwNotImpl[T](obj : T) = {
    throw new NotImplementedError(s"Support missing for ${obj.getClass}.")
  }
}
