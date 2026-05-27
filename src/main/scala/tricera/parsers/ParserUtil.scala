/**
 * Copyright (c) 2021-2023 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.parser.Parser2InputAbsy.CRRemover2
import tricera.concurrency.concurrent_c
import tricera.concurrency.concurrent_c.Absyn.{Afunc, Exp, ExprS, NewFunc, Progr, ScompTwo, SexprTwo}
import tricera.concurrency.concurrent_c.{Yylex, parser}
import tricera.concurrency.ccreader.CCExceptions._

object ParserUtil {
  def parseWithEntry[T](input : java.io.Reader,
                        entry : (parser) => T) : T = {
    val l = new Yylex(new CRRemover2 (input))
    val p = new parser(l, l.getSymbolFactory)

    try { entry(p) } catch {
      case e : Exception =>
        throw new ParseException(
          "At line " + String.valueOf(l.line_num()) +
            ", near \"" + l.buff() + "\" :" +
            "     " + e.getMessage())
    }
  }

  // parses the expression in programs of the form:
  // void foo() { expression ; }
  // this is done to overcome java-cup's limitation of a single entry point
  private def parseExpFromProg(input : java.io.Reader) : Exp = {
    def entry(parser : concurrent_c.parser) = {
      val parseTree = parser.pProgram
      try {
        parseTree.asInstanceOf[Progr].listexternal_declaration_.getFirst.
          asInstanceOf[Afunc].function_def_.asInstanceOf[NewFunc].
          compound_stm_.asInstanceOf[ScompTwo].liststm_.getFirst.
          asInstanceOf[ExprS].expression_stm_.asInstanceOf[SexprTwo].exp_
      } catch {
        case _ : Exception => throw new ParseException(
          "Input is not of the form: void foo() { expression ; }")
      }
    }
    parseWithEntry(input, entry _)
  }

  def parseExp(exp : String) : Exp = {
    parseExpFromProg(
      new java.io.BufferedReader (
        new java.io.StringReader("void foo () { "  + exp + "; }"))
    )
  }
}
