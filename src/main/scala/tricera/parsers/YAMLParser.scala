/**
 * Copyright (c) 2024 Zafer Esen. All rights reserved.
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

/**
 * A parser for SV-COMP style YAML (.yml) specification files.
 * @note The case classes should reflect the structure of the files, do not
 *       add any new value fields to the case classes.
 */
object YAMLParser {
  case class BMOption(language : String, data_model : String)
  case class BMPropertyFile(property_file    : String,
                            expected_verdict : Option[Boolean] = None,
                            subproperty      : Option[String] = None) {
    def isReachSafety = property_file.contains("unreach-call")
    def isMemSafety = property_file.contains("valid-memsafety")
    def isMemCleanup = property_file.contains("valid-memcleanup")
  }

  case class BenchmarkInfo(format_version : String,
                           input_files    : String,
                           properties     : List[BMPropertyFile],
                           options        : BMOption)

  def extractBenchmarkInfo(yamlFileName : String): Option[BenchmarkInfo] = {
    try {
      import net.jcazevedo.moultingyaml._
      object BenchmarkYamlProtocol extends DefaultYamlProtocol {
        implicit val propFormat   = yamlFormat3(BMPropertyFile)
        implicit val optFormat    = yamlFormat2(BMOption)
        implicit val bmInfoFormat = yamlFormat4(BenchmarkInfo)
      }
      import BenchmarkYamlProtocol._
      val src     = scala.io.Source.fromFile(yamlFileName)
      val yamlAst = src.mkString.stripMargin.parseYaml
      src.close
      Some(yamlAst.convertTo[BenchmarkInfo])
    } catch {
      case _ : Throwable => None
    }
  }
}