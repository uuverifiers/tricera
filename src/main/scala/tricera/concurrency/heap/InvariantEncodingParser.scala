/**
 * Copyright (c) 2025-2026 Zafer Esen. All rights reserved.
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

package tricera.concurrency.heap

import tricera.concurrency.ccreader.CCExceptions.TranslationException
import net.jcazevedo.moultingyaml._

object InvariantEncodingParser {
  case class Declaration(name          : String,
                         `type`        : String,
                         initial_value : Option[String])
  case class Argument   (name   : String,
                         `type` : String)
  case class Predicate  (name : String,
                         args : List[Argument])
  case class FunctionDef(return_type : String,
                         args        : List[Argument],
                         body        : String)
  case class ParsedEncoding(
    ptr_type     : String,
    global_decls : Option[List[Declaration]],
    predicates   : Option[List[Predicate]],
    init_code    : List[String],
    read_fn      : FunctionDef,
    write_fn     : FunctionDef,
    alloc_fn     : FunctionDef,
    free_fn      : FunctionDef
  )

  object EncodingYamlProtocol extends DefaultYamlProtocol {
    implicit val argumentFormat    : YamlFormat[Argument]       = yamlFormat2(Argument)
    implicit val declarationFormat : YamlFormat[Declaration]    = yamlFormat3(Declaration)
    implicit val predicateFormat   : YamlFormat[Predicate]      = yamlFormat2(Predicate)
    implicit val functionDefFormat : YamlFormat[FunctionDef]    = yamlFormat3(FunctionDef)
    implicit val encodingFormat    : YamlFormat[ParsedEncoding] = yamlFormat8(ParsedEncoding)
  }

  /**
   * Lists available encoding names by reading a generated listing file
   * from resources. The file is generated at compile time by sbt.
   */
  lazy val availableEncodings: Seq[String] = {
    val listPath = "tricera/heap/encodings/encodings.list"
    try {
      val stream = getClass.getClassLoader.getResourceAsStream(listPath)
      if (stream == null) Seq.empty
      else {
        val source = scala.io.Source.fromInputStream(stream)
        try {
          source.getLines().filter(_.nonEmpty).toSeq
        } finally source.close()
      }
    } catch {
      case _ : Throwable => Seq.empty
    }
  }

  def parse(encodingName : String) : ParsedEncoding = {
    val resourcePath = s"tricera/heap/encodings/$encodingName.yml"
    val inputStream = Option(getClass.getClassLoader.getResourceAsStream(resourcePath))
      .getOrElse {
        throw new TranslationException(
          s"Could not find encoding file for '$encodingName'. " +
          s"Expected to find it at 'resources/$resourcePath'")
      }
    val source = scala.io.Source.fromInputStream(inputStream)
    try {
      import EncodingYamlProtocol._
      val yamlAst = source.mkString.parseYaml
      yamlAst.convertTo[ParsedEncoding]
    } catch {
      case e: Throwable =>
        throw new TranslationException(s"Failed to parse encoding file for " +
                                       s"'$encodingName': $e")
    } finally {
      source.close()
    }
  }
}
