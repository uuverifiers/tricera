/**
 * Copyright (c) 2024 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package tricera.concurrency.ccreader

import ap.parser.IFormula
import ap.types.SortedConstantTerm
import tricera.Util.SourceInfo
import tricera.params.TriCeraParameters

sealed trait VariableStorage
case object GlobalStorage extends VariableStorage
case object AutoStorage   extends VariableStorage
case class  StaticStorage(enclosingFunctionName : String) extends VariableStorage

object CCVar {
  val lineNumberPrefix = ":"
}

class CCVar(val name    : String,
            val srcInfo : Option[SourceInfo],
            val typ     : CCType,
            val storage : VariableStorage) {
  import CCVar._
  val isStatic = storage.isInstanceOf[StaticStorage]
  val enclosingFunctionName : Option[String] = storage match {
    case GlobalStorage     => None
    case AutoStorage       => None // We could provide the enclosing function, but it is not needed.
    case s : StaticStorage => Some(s.enclosingFunctionName)
  }
  val nameWithLineNumber = name +
    (srcInfo match {
      case Some(info) if info.line >= 0 =>
        lineNumberPrefix + info.line
      case _ => ""
    })
  val sort = typ.toSort
  val term = {
    val termName =
      if (TriCeraParameters.get.showVarLineNumbersInTerms)
        nameWithLineNumber
      else name
    new SortedConstantTerm(termName, sort)
  }
  def rangePred: IFormula = typ rangePred term
  override def toString: String =
    if (TriCeraParameters.get.showVarLineNumbersInTerms)
      nameWithLineNumber
    else name
  def toStringWithLineNumbers: String = name + {
    srcInfo match {
      case Some(info) if info.line >= 0 => lineNumberPrefix + info.line
      case _                            => ""
    }
  }
}