/**
 * Copyright (c) 2021-2025 Zafer Esen. All rights reserved.
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

import tricera.Main

import sys.process.Process
import java.nio.file.{Files, Paths}

class TriCeraPreprocessor(val inputFilePath   : String,
                          val outputFilePath  : String,
                          val entryFunction   : String,
                          val displayWarnings : Boolean,
                          val quiet           : Boolean,
                          val determinize     : Boolean) {
  val ppPath : String = sys.env.get("TRI_PP_PATH") match {
    case Some(path) => path + "/tri-pp"
    case _ =>
      val path = Paths.get(System.getProperty("user.dir") + "/tri-pp")
      if (Files.exists(path)) path.toString
      else throw new Main.MainException("The preprocessor binary" +
        " (tri-pp) could not be found. Please ensure that the environment " +
        "variable TRI_PP_PATH is exported and points to the preprocessor's" +
        " base directory")
  }

  private def runPreprocessor(extraArgs : Seq[String],
                              errorMsg  : String,
                              input     : String,
                              output    : String) : Int = {
    val cmdLine : Seq[String] = Seq(ppPath, input, "-o", output) ++
                     (if (quiet) Seq("-q") else Nil) ++ extraArgs ++
                     Seq("-m", entryFunction, "--", "-xc") ++
                     (if (displayWarnings) Nil else Seq("-Wno-everything"))

    try { Process(cmdLine) ! } catch {
      case _: Throwable =>
        throw new Main.MainException(s"$errorMsg\nPreprocessor command: ${cmdLine.mkString(" ")}")
    }
  }

  private val initialReturnCode = runPreprocessor(
    Nil, "TriCera preprocessor could not be executed.", inputFilePath, outputFilePath)
  val hasError : Boolean = initialReturnCode != 0

  if (determinize) {
    val determinizeSteps = Seq(
      ("--make-calls-unique", "tri-pp failed while trying to make calls unique."),
      ("--determinize", "tri-pp failed while trying to make the program deterministic.")
    )

    determinizeSteps.foldLeft(0){
      case (_, (arg, msg)) =>
        runPreprocessor(Seq(arg), msg, outputFilePath, outputFilePath)
    }
  }
}
