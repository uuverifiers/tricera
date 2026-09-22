/**
 * Copyright (c) 2021-2026 Zafer Esen. All rights reserved.
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
import java.io.{File, IOException}
import java.nio.file.{Files, Path, Paths}
import java.util.concurrent.TimeUnit

object TriCeraPreprocessor {
  def findPreprocessor : Path = {
    val executable = if (sys.props.get("org.graalvm.nativeimage.imagecode").contains("runtime")) {
      val command = ProcessHandle.current().info().command()
      if (command.isPresent) Some(Paths.get(command.get())) else None
    } else None
    findPreprocessor(sys.env, Paths.get("").toAbsolutePath, executable)
  }

  private[concurrency] def findPreprocessor(env : Map[String, String], cwd : Path,
                                           executable : Option[Path]) : Path = {
    def usable(path : Path) = Files.isRegularFile(path) && Files.isExecutable(path)
    env.get("TRI_PP_PATH").filter(_.nonEmpty) match {
      case Some(directory) =>
        val path = cwd.resolve(directory).resolve("tri-pp")
        if (!usable(path)) throw new Main.MainException(
          "TRI_PP_PATH does not contain an executable tri-pp: " + path)
        path.normalize()
      case None =>
        val sibling = executable.toSeq.map(_.toAbsolutePath.getParent.resolve("tri-pp"))
        val onPath = env.get("PATH").toSeq.flatMap(_.split(File.pathSeparator, -1))
          .map(directory => cwd.resolve(directory).resolve("tri-pp"))
        (Seq(cwd.resolve("tri-pp")) ++ sibling ++ onPath).find(usable)
          .map(_.normalize()).getOrElse(throw new Main.MainException(
            "Could not find an executable tri-pp. Set TRI_PP_PATH to its directory, " +
            "place it in the current directory or beside TriCera, or add it to PATH."))
    }
  }

  def checkReady() : Path = checkReady(findPreprocessor, 5000)

  private[concurrency] def checkReady(path : Path, timeoutMillis : Long) : Path = {
    val process = try {
      new ProcessBuilder(path.toString, "--version")
        .redirectOutput(ProcessBuilder.Redirect.DISCARD)
        .redirectError(ProcessBuilder.Redirect.INHERIT).start()
    } catch {
      case e : IOException => throw new Main.MainException(
        "Could not execute tri-pp at " + path + ": " + e.getMessage)
    }
    try {
      if (!process.waitFor(timeoutMillis, TimeUnit.MILLISECONDS))
        throw new Main.MainException("Timed out checking tri-pp at " + path)
      if (process.exitValue() != 0)
        throw new Main.MainException(
          "tri-pp exited with status " + process.exitValue() + ": " + path)
      path
    } finally {
      if (process.isAlive) process.destroyForcibly()
    }
  }
}

class TriCeraPreprocessor(val inputFilePath   : String,
                          val outputFilePath  : String,
                          val entryFunction   : String,
                          val displayWarnings : Boolean,
                          val quiet           : Boolean,
                          val determinize     : Boolean,
                          val noDeclSlice     : Boolean = false) {
  private val factsFile : File = File.createTempFile("tri-facts-", ".yml")
  factsFile.deleteOnExit()

  val ppPath : String = TriCeraPreprocessor.findPreprocessor.toString

  private def runPreprocessor(extraArgs : scala.Seq[String],
                              errorMsg  : String,
                              input     : String,
                              output    : String) : Int = {
    val langFlag = if (inputFilePath.endsWith(".cpp")) "-xc++" else "-xc"
    val cmdLine : scala.Seq[String] = scala.Seq(ppPath, input, "-o", output) ++
                     (if (quiet) scala.Seq("-q") else Nil) ++
                     (if (noDeclSlice) scala.Seq("--no-decl-slice") else Nil) ++
                     extraArgs ++
                     scala.Seq(s"--facts=${factsFile.getAbsolutePath}") ++
                     scala.Seq("-m", entryFunction, "--", langFlag) ++
                     (if (displayWarnings) Nil else scala.Seq("-Wno-everything"))

    try { Process(cmdLine) ! } catch {
      case e : Throwable =>
        throw new Main.MainException("TriCera preprocessor could not" +
          " be executed at " + ppPath + ": " + e.getMessage + "\n" +
          "Preprocessor command: " + cmdLine
        )
    }
  }

  private val initialReturnCode = runPreprocessor(
    if (noDeclSlice) Seq("--no-decl-slice") else Nil,
    "TriCera preprocessor could not be executed.",
    inputFilePath, outputFilePath)
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

  // Facts about the produced program reported by tri-pp
  val facts : PreprocessorFacts =
    PreprocessorFacts.parseFile(factsFile.getAbsolutePath)
}

object PreprocessorFacts {
  val empty : PreprocessorFacts =
    PreprocessorFacts(usesThrow = false, usesTryCatch = false)

  // Parse a tri-pp facts (YAML) file. A missing file, unreadable content or an
  // absent key yields false for the corresponding fact (which will lead to
  // an error if it is inaccurate, but it should not be missing in the first place).
  def parseFile(path : String) : PreprocessorFacts =
    try {
      val src = scala.io.Source.fromFile(path)
      try parse(src.mkString) finally src.close()
    } catch { case _ : Throwable => empty }

  private def parse(text : String) : PreprocessorFacts = {
    import net.jcazevedo.moultingyaml._
    val fields = text.parseYaml.asYamlObject.fields
    def flag(key : String) : Boolean = fields.get(YamlString(key)) match {
      case Some(YamlBoolean(b)) => b
      case _                    => false
    }
    val typedefs : Map[String, String] =
      fields.get(YamlString("typedefs")) match {
        case Some(YamlArray(entries)) =>
          entries.flatMap {
            case YamlObject(m) =>
              (m.get(YamlString("name")), m.get(YamlString("underlying"))) match {
                case (Some(YamlString(n)), Some(YamlString(u))) => Some(n -> u)
                case _                                          => None
              }
            case _ => None
          }.toMap
        case _ => Map.empty
      }
    PreprocessorFacts(flag("usesThrow"), flag("usesTryCatch"), typedefs)
  }
}

case class PreprocessorFacts(usesThrow : Boolean, usesTryCatch : Boolean,
                             typedefs : Map[String, String] = Map.empty) {
  def usesExceptions : Boolean = usesThrow || usesTryCatch
}
