/**
 * Copyright (c) 2025 Zafer Esen.
 * All rights reserved.
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

package tricera

import java.io.File
import java.nio.file.{Files, StandardCopyOption}
import sys.process._
import tricera.concurrency.CCReader

object CPreprocessor {
  /**
   * Preprocesses fileName using the C preprocessor.
   */
  def apply(fileName             : String,
            includeSystemHeaders : Boolean,
            arithMode            : CCReader.ArithmeticMode.Value) : String = {
    val preprocessedFile = File.createTempFile("tri-", ".i")
    preprocessedFile.deleteOnExit()

    var cmdLine: Seq[String] = null
    try {
      val errorSuppressingLogger = ProcessLogger(_ => (), _ => ())
      if (!includeSystemHeaders) {
        val macroHeaderTempFile: File = {
          val resourcePath = arithMode match {
            case CCReader.ArithmeticMode.Mathematical => "tricera/headers/macros_math.h"
            case CCReader.ArithmeticMode.ILP32        => "tricera/headers/macros_ilp32.h"
            case CCReader.ArithmeticMode.LP64         => "tricera/headers/macros_lp64.h"
            case CCReader.ArithmeticMode.LLP64        => "tricera/headers/macros_llp64.h"
          }

          val inputStream = Option(getClass.getClassLoader.getResourceAsStream(resourcePath))
            .getOrElse {
              throw new Main.MainException(
                s"Could not find macro header for '$arithMode'. Expected in resources/$resourcePath"
                )
            }

          val tmpFile = Files.createTempFile("tricera-macros-", ".h").toFile
          tmpFile.deleteOnExit()
          Files.copy(inputStream, tmpFile.toPath, StandardCopyOption.REPLACE_EXISTING)
          inputStream.close()
          tmpFile
        }

        cmdLine = Seq("cpp", "-E", "-P", "-CC", "-nostdinc", "-undef")
        val pipedInput = s"""#include "${macroHeaderTempFile.getAbsolutePath}"\n#include "$fileName"""""
        val inputStream = new java.io.ByteArrayInputStream(pipedInput.getBytes)
        (Process(cmdLine) #< inputStream #> preprocessedFile).!(errorSuppressingLogger)
      } else {
        cmdLine = Seq("cpp", fileName, "-E", "-P", "-CC")
        (Process(cmdLine) #> preprocessedFile).!(errorSuppressingLogger)
      }
    } catch {
      case t : Throwable =>
        throw new Main.MainException(
          "The C preprocessor could not be executed. " +
          "This might be due to cpp not being installed in the system.\n" +
          "Attempted command: " + (if (cmdLine != null) cmdLine.mkString(" ") else "N/A")
          )
    }
    preprocessedFile.getAbsolutePath
  }
}
