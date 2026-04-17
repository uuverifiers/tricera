/**
 * Copyright (c) 2021-2022 Pontus Ernstedt
 *               2023-2026 Zafer Esen. All rights reserved.
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

package tricera.acsl

import ap.parser.{IFormula, ITerm}
import tricera.Util.SourceInfo
import tricera.concurrency.ccreader.{CCType, CCVar}

trait ParsedAnnotation

// todo: make case class?
class FunctionContract(
  val pre  : IFormula,
  val post : IFormula,
  val assignsAssert : IFormula,
  val assignsAssume : IFormula,
  val srcInfo       : SourceInfo,
  val postSrcInfo   : SourceInfo) extends ParsedAnnotation {
  override def toString : String = {
    s"""|requires ${ap.SimpleAPI.pp(pre)}
        |ensures  ${ap.SimpleAPI.pp(post)}
        |assigns (in asserts) ${ap.SimpleAPI.pp(assignsAssert)}
        |assigns (in assumes) ${ap.SimpleAPI.pp(assignsAssume)}
        |""".stripMargin
  }
}

case class StatementAnnotation(f        : IFormula,
                               isAssert : Boolean) extends ParsedAnnotation

case class LoopAnnotation(invariant : IFormula) extends ParsedAnnotation

case class GhostBlock(items   : scala.Seq[GhostItem],
                      srcInfo : SourceInfo) extends ParsedAnnotation

sealed trait GhostItem { def srcInfo : SourceInfo }

case class GhostDeclaration(ccVar   : CCVar,
                            initOpt : Option[ITerm],
                            srcInfo : SourceInfo) extends GhostItem

case class GhostAssignment(lhs     : GhostLValue,
                           rhs     : ITerm,
                           srcInfo : SourceInfo) extends GhostItem

sealed trait GhostLValue
case class GhostLValIdent(name : String) extends GhostLValue
case class GhostLValArray(inner : GhostLValue, idx : ITerm)
  extends GhostLValue
case class GhostLValField(inner : GhostLValue, field : String)
  extends GhostLValue
case class GhostLValArrow(inner : GhostLValue, field : String)
  extends GhostLValue
case class GhostLValDeref(inner : GhostLValue) extends GhostLValue
