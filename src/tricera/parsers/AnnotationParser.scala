/**
 * Copyright (c) 2021-2022 Zafer Esen. All rights reserved.
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

package tricera.parsers

import scala.util.parsing.combinator._
import tricera.concurrency.concurrent_c.Absyn._

sealed class AnnotationParserError (msg: String)

/**
 * Parses hint annotations. If an annotation cannot be parsed, it is returned
 * as a MaybeACSLAnnotation.
 */
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
  case class  MaybeACSLAnnotation(annot : String,
                                  msg   : String)       extends AnnotationInfo

  private def parseAnnotation: Parser[AnnotationInfo] = {
    cident ~ maybe_cost ~ maybe_exp_args
  } ^^ {
    case s ~ mCost ~ mArgs if hintKeywords.keys.exists(_ == s) =>
      AbsHintClause(hintKeywords(s), mCost, mArgs)
    case "contract" ~ None ~ None =>
      ContractGen
    case s ~ None ~ None => // other cases
      MaybeACSLAnnotation(s, "")
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
      case NoSuccess(msg, _)  => Seq(MaybeACSLAnnotation(annotation, msg))
      case Success(result, _) => result
    }
  }
}
