/**
 * Copyright (c) 2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package tricera.concurrency

import tricera.concurrency.ccreader.CCExceptions
import tricera.concurrency.concurrent_c.Absyn._

import java.io.{Reader, StringReader}

object ParseUtil {
  def parseGlobalDeclaration(input : Reader) : Dec = {
    def entry(parser : concurrent_c.parser) = {
      val parseTree = parser.pProgram()
      parseTree match {
        case p : Progr if p.listexternal_declaration_.size == 1 =>
          p.listexternal_declaration_.getFirst match {
            case global : Global => global.dec_
            case _ => throw new Exception("Input is not a global declaration")
          }
        case _ => throw new Exception(
          "Input is not a global declaration")
      }
    }
    CCReader.parseWithEntry(input, entry)
  }

  def parseFunctionDefinition(input: Reader): External_declaration = {
    def entry(parser: concurrent_c.parser) = {
      val parseTree = parser.pProgram()
      parseTree match {
        case p: Progr if p.listexternal_declaration_.size == 1 =>
          p.listexternal_declaration_.getFirst match {
            case f: Afunc => f
            case _ => throw new Exception("Input is not a function definition")
          }
        case _ => throw new Exception("Input is not a function definition")
      }
    }
    CCReader.parseWithEntry(input, entry)
  }

  def parseStatement(input: java.io.Reader): Stm = {
    val statementText = new java.util.Scanner(input).useDelimiter("\\A").next()

    val programText = s"void dummy() { $statementText }"
    val programReader = new java.io.StringReader(programText)

    def entry(parser: concurrent_c.parser): Stm = {
      val programAst = parser.pProgram()
      programAst match {
        case p: Progr =>
          val funcExtDecl = p.listexternal_declaration_.getFirst.asInstanceOf[Afunc]
          val funcDef = funcExtDecl.function_def_
          val body = CCReader.FuncDef(funcDef).body.asInstanceOf[ScompTwo]

          if (body.liststm_.size != 1) {
            throw new Exception(
              s"Internal parser error: Expected to parse one statement, but found ${body.liststm_.size}. " +
              s"Original text: '$statementText'")
          }
          body.liststm_.getFirst

        case _ =>
          throw new Exception(s"Internal parser error: Could not parse wrapped statement: '$statementText'")
      }
    }

    try {
      CCReader.parseWithEntry(programReader, entry)
    } catch {
      case e: Exception =>
        throw new CCExceptions.ParseException(
          s"Failed to parse statement string: '$statementText'. Reason: ${e.getMessage}")
    }
  }

  def parseExpression(input: java.io.Reader): Exp = {
    val expressionText = new java.util.Scanner(input).useDelimiter("\\A").next()
    // Wrap in a dummy function and extract.
    val programText = s"void __dummy_func() { ($expressionText); }"

    def entry(parser: concurrent_c.parser): Exp = {
      parser.pProgram() match {
        case p: Progr =>
          val func = p.listexternal_declaration_.getFirst.asInstanceOf[Afunc].function_def_
          val body = CCReader.FuncDef(func).body.asInstanceOf[ScompTwo]
          val stmt = body.liststm_.getFirst.asInstanceOf[ExprS]
          stmt.expression_stm_.asInstanceOf[SexprTwo].exp_
      }
    }
    CCReader.parseWithEntry(new StringReader(programText), entry)
  }

  /**
   * Parses the "/* INPUT: ... */" comment from the raw program text.
   * This is produced by tri-pp when using the [[InvariantEncodingModel]] for heap.
   * @param programText The full content of the C source file.
   * @return A sequence of input variable names found, or an empty sequence if not found.
   */
  def parseInputComment(programText : String) : Seq[String] = {
    val pattern = """/\*\s*INPUT:\s*([^/\\*]+)\*/""".r
    pattern.findFirstMatchIn(programText) match {
      case Some(m) =>
        m.group(1).split(',').map(_.trim).filter(_.nonEmpty).toSeq
      case None =>
        Seq.empty
    }
  }
}
