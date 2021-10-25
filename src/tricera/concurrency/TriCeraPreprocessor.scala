package tricera.concurrency

import tricera.Main

import sys.process._
import sys.env
import java.nio.file.{Paths, Files}

class TriCeraPreprocessor(val inputFilePath : String,
                          val outputFilePath : String,
                          val displayWarnings : Boolean,
                          val quiet : Boolean) {
  val ppPath = sys.env.get("TRI_PP_PATH") match {
    case Some(path) => path + "/tri-pp"
    case _ =>
      val path = Paths.get(System.getProperty("user.dir") + "/tri-pp")
      if (Files.exists(path)) path
      else
        throw new Main.MainException("The preprocessor binary" +
        " (tri-pp) could not be found. Please ensure that the environment " +
        "variable TRI_PP_PATH is exported and points to the preprocessor's" +
        " base directory")
  }
  private val cmdLine = List(
    ppPath,
    inputFilePath,
    "-o " + outputFilePath,
    if(quiet) "-q" else "",
    "--",
    "-xc",
    if(displayWarnings) "" else "-Wno-everything"
    ).mkString(" ")
  val returnCode =
    try { cmdLine !}
    catch {
      case _: Throwable =>
        throw new Main.MainException("The preprocessor could not" +
          " be executed. This might be due to TriCera preprocessor binary " +
          "not being in the current directory. Alternatively, use the " +
          "-noPP switch to disable the preprocessor.\n" +
          "Preprocessor command: " + cmdLine
        )
    }
  val hasError = returnCode != 0
}