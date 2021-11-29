package tricera.acsl

import tricera.acsl._
import tricera.acsl.{Absyn => AST};

import collection.JavaConverters._

import ap.parser.IExpression
import ap.parser.{IConstant, ITerm, IIntLit, IBoolLit, IFormula, IFormulaITE}

class ACSLParseException(msg : String) extends Exception(msg)
class ACSLTranslateException(msg : String) extends Exception(msg)

object ACSLTranslator {
  private def throwNotImpl[T](obj : T) = {
    throw new NotImplementedError(s"Support missing for ${obj.getClass}.")
  }

  def translateContract(annot : String/*, context : Context*/) : FunctionContract = {
    val l : Yylex = new Yylex(new java.io.StringReader(preprocess(annot)))
    val p : parser = new parser(l, l.getSymbolFactory())
    try {
      val ast : AST.Annotation = p.pAnnotation()
      ast match {
        case ac : AST.AnnotContract => translate(ac.functioncontract_)
        case _ => throw new ACSLParseException("Not a contract annotation.")
      }
    } catch {
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
    case p : AST.PredLocalBinding     => throwNotImpl(p)
    case p : AST.PredLocalBinding2    => throwNotImpl(p)
    case p : AST.PredForAll           => throwNotImpl(p)
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
    case t : AST.TermUnaryOp                 => throwNotImpl(t)
    case t : AST.TermBinOp                   => throwNotImpl(t)
    case t : AST.TermArrayAccess             => throwNotImpl(t)
    case t : AST.TermArrayFunctionalModifier => throwNotImpl(t)
    case t : AST.TermStructFieldAccess       => throwNotImpl(t)
    case t : AST.TermFieldFunctionalModifier => throwNotImpl(t)
    case t : AST.TermStructPtrFieldAccess    => throwNotImpl(t)
    case t : AST.TermTypeCast                => throwNotImpl(t)
    case t : AST.TermFuncAppl                => throwNotImpl(t)
    case t : AST.TermParentheses             => throwNotImpl(t)
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
    val id = term.id_
    // TODO: Lookup if var exists in scope (or as local binding) first.
    //       If so, use either same or equivalent MonoSortedConstant?
    //       Otherwise, parse error.
    IConstant(new IExpression.ConstantTerm(id))
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
}
