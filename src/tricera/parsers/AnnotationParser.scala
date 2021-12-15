package tricera.parsers

import tricera.acsl.{ACSLTranslator, FunctionContract}

import scala.util.parsing.combinator._
import tricera.concurrency.concurrent_c.Absyn._

sealed class AnnotationParserError (msg: String)

object AnnotationParser extends RegexParsers {
  override def skipWhitespace: Boolean = true

  sealed abstract class Hint
  case object Predicates    extends Hint
  case object PredicatesTpl extends Hint
  case object TermsTpl      extends Hint
  val hintKeywords = Map(("predicates", Predicates),
    ("predicates_tpl", PredicatesTpl),
    ("terms_tpl", TermsTpl))

  sealed abstract trait AnnotationInfo
  case class AbsHintClause(hint      : Hint,
                           cost     : Option[String],
                           exp_args : Option[Exp])      extends AnnotationInfo
  case object ContractGen                               extends AnnotationInfo
  case class  InvalidAnnotation (annot : String,
                                 msg   : String)        extends AnnotationInfo

  private def parseAnnotation: Parser[AnnotationInfo] = {
    cident ~ maybe_cost ~ maybe_exp_args
  } ^^ {
    case s ~ mCost ~ mArgs if hintKeywords.keys.exists(_ == s) =>
      AbsHintClause(hintKeywords(s), mCost, mArgs)
    case "contract" ~ None ~ None =>
      ContractGen
    case s ~ None ~ None => // other cases
      InvalidAnnotation(s, "")
  }

  def cident: Parser[String] = {
    "[a-zA-Z_$][a-zA-Z0-9_$]*".r ^^ { str => str }
  }

  def unboundedInteger: Parser[String] = {
    "[1-9][0-9]*".r ^^ { str => str }
  }

  def maybe_cost: Parser[Option[String]] = {
    opt("[" ~ unboundedInteger ~ "]")
  } ^^ {
    case Some(_ ~ value ~ _) => Some(value)
    case _ => None
  }

  def maybe_exp_args: Parser[Option[Exp]] = {
    opt("{" ~ literalWithoutBraces ~ "}")
  } ^^ {
    case Some(_ ~ expStr ~ _) =>
      try Some(ParserUtil.parseExp(expStr)) catch {
        case _ : Exception => None
      }
    case _ => None
  }

  def literalWithoutBraces: Parser[String] = """[^\{^\}]+""".r ^^ { str => str }

  def apply (annotation : String) : Seq[AnnotationInfo] = {
    parse(phrase(rep1(parseAnnotation)), annotation) match {
      case NoSuccess(msg, _)  => Seq(InvalidAnnotation(annotation, msg))
      case Success(result, _) => result
    }
  }
}