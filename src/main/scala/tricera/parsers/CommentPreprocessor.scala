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
import java.io.{BufferedReader, BufferedWriter, StringReader, StringWriter}
import tricera.Literals

// preprocesses ACSL style comments to make life easier for the parser.
object CommentPreprocessor {
  val annotationMarker   = Literals.annotationMarker
  val ghostOpenMarker    = Literals.ghostOpenMarker
  val ghostCloseMarker   = Literals.ghostCloseMarker

  private val ghostKeyword = "ghost"

  private def ghostKeywordEnd(s : String) : Int = {
    var i = 0
    while (i < s.length && (s.charAt(i) == ' ' || s.charAt(i) == '\t')) i += 1
    val end = i + ghostKeyword.length
    if (end > s.length) return -1
    if (s.substring(i, end) != ghostKeyword) return -1
    if (end < s.length) {
      val c = s.charAt(end)
      if (c.isLetterOrDigit || c == '_' || c == '$') return -1
    }
    end
  }

  def apply(reader : BufferedReader, readerBufferSize : Int = 1000) :
  BufferedReader = {
    val stringWriter = new StringWriter(readerBufferSize)
    val writer = new BufferedWriter(stringWriter)

    var isInComment = false
    var currentClose = annotationMarker

    var line: String = reader.readLine
    val newLine = new scala.collection.mutable.StringBuilder(line.length)
    var curInd = 0

    while (line != null) {
      if (!isInComment) {
        val curSlashInd = line.indexOf("/", curInd)
        curSlashInd match {
          case -1 => // no more slashes
            newLine ++= line.substring(curInd)
            curInd = line.length // will move on to next line
          case i if i < line.length - 2 => // need at least 2 more chars
            line.substring(i + 1, i + 3) match {
              case "*@" =>
                val gEnd = ghostKeywordEnd(line.substring(i + 3))
                if (gEnd >= 0) {
                  // /*@ ghost <body> */
                  newLine ++= line.substring(curInd, i) ++ ghostOpenMarker
                  isInComment = true
                  currentClose = ghostCloseMarker
                  curInd = i + 3 + gEnd
                } else {
                  // Ordinary hint/contract annotation.
                  newLine ++= line.substring(curInd, i) ++ annotationMarker
                  isInComment = true
                  currentClose = annotationMarker
                  curInd = i + 3
                }
              case "/@" =>
                val gEnd = ghostKeywordEnd(line.substring(i + 3))
                if (gEnd >= 0) {
                  // //@ ghost <body>
                  newLine ++= line.substring(curInd, i) ++ ghostOpenMarker ++
                    line.substring(i + 3 + gEnd) ++ ghostCloseMarker
                } else {
                  newLine ++= line.substring(curInd, i) ++ annotationMarker ++
                    line.substring(i + 3) ++ annotationMarker
                }
                curInd = line.length // will move on to next line
              case _ => // found slash but not a comment in our desired format
                newLine ++= line.substring(curInd, i + 1)
                curInd = i + 1
            }
          case _ =>
            newLine ++= line.substring(curInd)
            curInd = line.length
        }
      } else { // is in block commment
        val curStarInd = line.indexOf("*", curInd) // try to find a closing comment
        curStarInd match {
          case -1 => // nothing found
            newLine ++= line.substring(curInd)
            curInd = line.length // will move on to next line
          case i if i < line.length - 1 && line.charAt(i + 1) == '/' && // "@*/" found
            i > 0 && line.charAt(i - 1) == '@' =>
            newLine ++= line.substring(curInd, i - 1) + currentClose
            curInd = i + 2
            isInComment = false
          case i if i < line.length - 1 && line.charAt(i + 1) == '/' => // "*/" found
            newLine ++= line.substring(curInd, i) ++ currentClose
            curInd = i + 2
            isInComment = false
          case i => // found a star, but was not for closing the comment
            newLine ++= line.substring(curInd, i + 1)
            curInd = i + 1
        }
      }
      if (curInd >= line.length) {
        line = reader.readLine
        writer.write(newLine.toString ++ "\n") //(if(isInComment) "" else "\n")) // remove new lines as well?
        newLine.clear
        curInd = 0
      }
    }
    stringWriter.close()
    writer.close()

//    println("comment-preprocessed input:\n\n" + stringWriter.getBuffer.toString)

    new BufferedReader(new StringReader(
      rewriteGhostLogicTypes(stringWriter.getBuffer.toString)))
    // todo: benchmark this with files, >1 MB, benchmark this whole class
  }

  // ACSL treats `integer` and `boolean` as logic-type keywords
  // inside annotations. Regular C code may still use them as plain
  // identifiers. Rewrite them to internal (`$MathInt`, `_Bool`)
  private val ghostSpanRegex =
    new scala.util.matching.Regex(
      java.util.regex.Pattern.quote(ghostOpenMarker) + "(.*?)" +
      java.util.regex.Pattern.quote(ghostCloseMarker), "body")
  private def rewriteGhostLogicTypes(s : String) : String =
    ghostSpanRegex.replaceAllIn(s, m => {
      val body = m.group("body")
        .replaceAll("\\binteger\\b", "\\$MathInt")
        .replaceAll("\\bboolean\\b", "_Bool")
      java.util.regex.Matcher.quoteReplacement(
        ghostOpenMarker + body + ghostCloseMarker)
    })
}
