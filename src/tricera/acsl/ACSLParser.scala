package tricera.acsl;

import tricera.acsl._;
import tricera.acsl.Absyn._;
//import tricera.acsl.{Absyn => ASTNode};
import scala.collection.mutable.{ArrayBuffer, Buffer, Stack, HashMap => MHashMap}

import tricera.Util._
import collection.JavaConverters._
import ap.parser.IExpression
import ap.parser.{IConstant, ITerm, IIntLit, IBoolLit, IFormula, IFormulaITE}

class ACSLParseException(msg : String) extends Exception(msg)

// class Context

object ACSLTranslator {

  private def throwNotImpl[T](obj : T) = {
    throw new NotImplementedError(s"Support missing for ${obj.getClass}.")
  }

  def translateContract(annot : String) : (IExpression, IExpression) = {
    // IDEA: Can we reuse `l` and `p` (as fields)?
    val l : Yylex = new Yylex(new java.io.StringReader(annot))
    val p : parser = new parser(l, l.getSymbolFactory())
    try {
      val ast : Annotation = p.pAnnotation()
      val contract = ast match {
        case ac : AnnotContract => translate(ac.functioncontract_)
        case _ => throw new ACSLParseException("Not a contract annotation.")
      }
      contract 

    } catch {
      case e : Exception =>
        throw new ACSLParseException(
          "At line " + String.valueOf(l.line_num()) +
          ", near \"" + l.buff() + "\" :" +
          "     " + e.getMessage()
        )
    }
  }

// ---- Contracts ------------------------------------------
  def translate(contract : FunctionContract) : (IFormula, IFormula) = contract match {
    case c : Contract =>
      val requiresClauses = c.listrequiresclause_.asScala.toList
      val preCond = IExpression.and(requiresClauses.map(translate))

      val simpleClauses = c.listsimpleclause_.asScala.toList
      val (ensuresClauses, assignsClauses) = simpleClauses.partition(sc => {
        sc.isInstanceOf[SimpleClauseEnsures]
      })
      val postCond = IExpression.and(ensuresClauses.map(translate))
      (preCond, postCond)

    case _ => throwNotImpl(contract)
  }

  def translate(clause : SimpleClause) : IFormula = clause match {
    case ac : SimpleClauseAssigns => throwNotImpl(ac)
    case ec : SimpleClauseEnsures => translate(ec.ensuresclause_)
  }

  
  def translate(clause : EnsuresClause) : IFormula = {
    translate(clause.asInstanceOf[AnEnsuresClause].predicate_)
  }

  def translate(clause : RequiresClause) : IFormula = clause match {
    case c : ARequiresClause => translate(c.predicate_) 
    case _ => throwNotImpl(clause) // NOTE: Shouldn't happen?
  }

// ---- Predicates -----------------------------------------
  def translate(pred : Predicate) : IFormula = pred match {
    case p : PredTrue             => translate(p)
    case p : PredFalse            => translate(p)
    case p : PredRelOp            => translate(p)
    case p : PredApplication      => throwNotImpl(p)
    case p : PredParentheses      => translate(p)
    case p : PredConjunction      => translate(p)
    case p : PredDisjunction      => translate(p)
    case p : PredImplication      => translate(p)
    case p : PredEquivalence      => translate(p)
    case p : PredNegation         => translate(p)
    case p : PredXOr              => translate(p)
    case p : PredTernaryCond      => throwNotImpl(p)
    case p : PredTernaryCond2     => translate(p)
    case p : PredLocalBinding     => throwNotImpl(p)
    case p : PredLocalBinding2    => throwNotImpl(p)
    case p : PredForAll           => throwNotImpl(p)
    case p : PredExists           => throwNotImpl(p)
    case p : PredSyntacticNaming  => translate(p)
    case p : PredSyntacticNaming2 => translate(p)
    case p : PredicateOld         => throwNotImpl(p)
  }

  def translate(pred : PredTrue) : IFormula = {
    IBoolLit(true)
  }

  def translate(pred : PredFalse) : IFormula = {
    IBoolLit(false)
  }

  def translate(pred : PredRelOp) : IFormula = {
    val left  : ITerm = translate(pred.term_1)
    val right : ITerm = translate(pred.term_2)
    pred.relop_ match {
      case op : RelOpEQ  => left === right 
      case op : RelOpNEQ => left =/= right
      case op : RelOpLEQ => left <= right
      case op : RelOpGEQ => left >= right
      case op : RelOpGT  => left > right
      case op : RelOpLT  => left < right
    }
  }

  def translate(pred : PredParentheses) : IFormula = {
    translate(pred.predicate_)
  }

  // NOTE: Might wanna simplify directly with e.g. &&&.
  def translate(pred : PredConjunction) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left & right
  }

  def translate(pred : PredDisjunction) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left | right
  }

  def translate(pred : PredImplication) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left ==> right
  }

  def translate(pred : PredEquivalence) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left <=> right
  }

  def translate(pred : PredNegation) : IFormula = {
    val right : IFormula = translate(pred.predicate_)
    right.unary_!
  }

  def translate(pred : PredXOr) : IFormula = {
    val left  : IFormula = translate(pred.predicate_1)
    val right : IFormula = translate(pred.predicate_2)
    left </> right
  }

  // How will this clash with `PredTernaryCond`?
  def translate(pred : PredTernaryCond2) : IFormula = {
    val cond  : IFormula = translate(pred.predicate_1)
    val left  : IFormula = translate(pred.predicate_2)
    val right : IFormula = translate(pred.predicate_3)
    IFormulaITE(cond, left, right)
  }

  // `INamedPart` relevant?
  def translate(pred : PredSyntacticNaming) : IFormula = {
    translate(pred.predicate_)
  }

  def translate(pred : PredSyntacticNaming2) : IFormula = {
    translate(pred.predicate_)
  }

// ---- Terms ----------------------------------------------
  def translate(term : Term) : ITerm = term match {
    case t : TermLiteral                 => translate(t)
    case t : TermIdent                   => translate(t)
    case t : TermUnaryOp                 => throwNotImpl(t)
    case t : TermBinOp                   => throwNotImpl(t)
    case t : TermArrayAccess             => throwNotImpl(t)
    case t : TermArrayFunctionalModifier => throwNotImpl(t)
    case t : TermStructFieldAccess       => throwNotImpl(t)
    case t : TermFieldFunctionalModifier => throwNotImpl(t)
    case t : TermStructPtrFieldAccess    => throwNotImpl(t)
    case t : TermTypeCast                => throwNotImpl(t)
    case t : TermFuncAppl                => throwNotImpl(t)
    case t : TermParentheses             => throwNotImpl(t)
    case t : TermTernaryCond             => throwNotImpl(t)
    case t : TermLocalBinding            => throwNotImpl(t)
    case t : TermSizeOfTerm              => throwNotImpl(t)
    case t : TermSizeOfType              => throwNotImpl(t)
    case t : TermSyntacticNaming         => throwNotImpl(t)
    case t : TermSyntacticNaming2        => throwNotImpl(t)
    case t : TermOld                     => throwNotImpl(t)
    case t : TermResult                  => throwNotImpl(t)
  }

  def translate(term : TermLiteral) : ITerm = {
    translate(term.literal_)
  }

  def translate(term : TermIdent) : ITerm = {
    val id = term.id_
    // TODO: I think idents can also be local bindings, 
    //       so need to scan context first.
    IConstant(new IExpression.ConstantTerm(id))
  }

// ---- Literals -------------------------------------------
  def translate(literal : Literal) : ITerm = literal match {
    // Do we want to use CCTypes here or what?
    case l : LiteralTrue   => throwNotImpl(l)
    case l : LiteralFalse  => throwNotImpl(l)
    case l : LiteralInt    => translate(l)
    case l : LiteralReal   => throwNotImpl(l)
    case l : LiteralString => throwNotImpl(l)
    case l : LiteralChar   => throwNotImpl(l)
  }

  def translate(li : LiteralInt) : ITerm = {
    // FIXME: Unsure if this is semantically correct with integer types and all.
    //        Probably need to know ArithmeticMode as context.
    IExpression.i(li.integer_)
  }
}
