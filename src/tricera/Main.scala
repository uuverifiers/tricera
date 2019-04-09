/**
  * Copyright (c) 2011-2019 Hossein Hojjat, Filip Konecny, Philipp Ruemmer,
  * Pavle Subotic. All rights reserved.
  *
  * Redistribution and use in source and binary forms, with or without
  * modification, are permitted provided that the following conditions are met:
  *
  * * Redistributions of source code must retain the above copyright notice, this
  * list of conditions and the following disclaimer.
  *
  * * Redistributions in binary form must reproduce the above copyright notice,
  * this list of conditions and the following disclaimer in the documentation
  * and/or other materials provided with the distribution.
  *
  * * Neither the name of the authors nor the names of their
  * contributors may be used to endorse or promote products derived from
  * this software without specific prior written permission.
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

import tricera.concurrency.CCReader
import java.io.{FileInputStream, InputStream, FileNotFoundException}
import lazabs.prover._
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.GlobalParameters

object TriCeraParameters {
  def get : TriCeraParameters =
    GlobalParameters.get.asInstanceOf[TriCeraParameters]
  val parameters =
    GlobalParameters.parameters
}

class TriCeraParameters extends GlobalParameters {

  var arithMode : CCReader.ArithmeticMode.Value =
    CCReader.ArithmeticMode.Mathematical

  protected def copyTo(that : TriCeraParameters) = {
    super.copyTo(that)
    that.arithMode = this.arithMode
  }

  override def clone: TriCeraParameters = {
    val res = new TriCeraParameters
    this copyTo res
    res
  }

  override def withAndWOTemplates : Seq[TriCeraParameters] =
    for (p <- super.withAndWOTemplates) yield p.asInstanceOf[TriCeraParameters]

}

////////////////////////////////////////////////////////////////////////////////

object Main {
  def assertions = GlobalParameters.get.assertions

  class MainException(msg: String) extends Exception(msg)

  object TimeoutException extends MainException("timeout")

  object StoppedException extends MainException("stopped")

  def openInputFile {
    val params = TriCeraParameters.get
    import params._
    in = new FileInputStream(fileName)
  }

  def main(args: Array[String]): Unit = doMain(args, false)

  val greeting =
    "TriCera v0.1.\n(C) Copyright 2012-2019 Zafer Esen, Hossein Hojjat, and Philipp Ruemmer"

  def doMain(args: Array[String],
             stoppingCond: => Boolean): Unit = try {
    val params = new TriCeraParameters
    GlobalParameters.parameters.value = params

    // work-around: make the Princess wrapper thread-safe
    lazabs.prover.PrincessWrapper.newWrapper

    import params._

    def arguments(args: List[String]): Boolean = args match {
      case Nil => true
      //case "-c" :: rest => drawCFG = true; arguments(rest)
      //case "-r" :: rest => drawRTree = true; arguments(rest)
      case "-f" :: rest => absInFile = true; arguments(rest)
      case "-p" :: rest => prettyPrint = true; arguments(rest)
      case "-pIntermediate" :: rest => printIntermediateClauseSets = true; arguments(rest)
      case "-sp" :: rest => smtPrettyPrint = true; arguments(rest)
      //      case "-pnts" :: rest => ntsPrint = true; arguments(rest)
      case "-horn" :: rest => horn = true; arguments(rest)
      case "-glb" :: rest => global = true; arguments(rest)
      case "-disj" :: rest => disjunctive = true; arguments(rest)
      case "-sol" :: rest => displaySolutionProlog = true; arguments(rest)
      case "-ssol" :: rest => displaySolutionSMT = true; arguments(rest)

      case "-abstract" :: rest => templateBasedInterpolation = true; arguments(rest)
      case "-abstractPO" :: rest => templateBasedInterpolationPortfolio = true; arguments(rest)
      case "-abstract:manual" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Empty
        arguments(rest)
      }
      case "-abstract:term" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Term
        arguments(rest)
      }
      case "-abstract:oct" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Octagon
        arguments(rest)
      }
      case "-abstract:relEqs" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.RelationalEqs
        arguments(rest)
      }
      case "-abstract:relIneqs" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.RelationalIneqs
        arguments(rest)
      }
      case "-abstract:off" :: rest => {
        templateBasedInterpolation = false
        arguments(rest)
      }
      case tTimeout :: rest if (tTimeout.startsWith("-abstractTO:")) =>
        templateBasedInterpolationTimeout =
          (java.lang.Float.parseFloat(tTimeout.drop(12)) * 1000).toInt;
        arguments(rest)

      case tFile :: rest if (tFile.startsWith("-hints:")) => {
        cegarHintsFile = tFile drop 7
        arguments(rest)
      }

      case "-splitClauses" :: rest => splitClauses = true; arguments(rest)

      case aMode :: rest if (aMode startsWith "-arithMode:") => {
        arithMode = aMode match {
          case "-arithMode:math" => CCReader.ArithmeticMode.Mathematical
          case "-arithMode:ilp32" => CCReader.ArithmeticMode.ILP32
          case "-arithMode:lp64" => CCReader.ArithmeticMode.LP64
          case "-arithMode:llp64" => CCReader.ArithmeticMode.LLP64
          case _ =>
            throw new MainException("Unrecognised mode " + aMode)
        }
        arguments(rest)
      }

      case "-n" :: rest => spuriousness = false; arguments(rest)
      //      case "-i" :: rest => interpolation = true; arguments(rest)
      case "-lbe" :: rest => lbe = true; arguments(rest)

      case arrayQuans :: rest if (arrayQuans.startsWith("-arrayQuans:")) =>
        if (arrayQuans == "-arrayQuans:off")
          arrayQuantification = None
        else
          arrayQuantification = Some(arrayQuans.drop(12).toInt)
        arguments(rest)

      case "-noSlicing" :: rest => slicing = false; arguments(rest)
      //case "-array" :: rest => arrayRemoval = true; arguments(rest)
      case "-princess" :: rest => princess = true; arguments(rest)
      case "-stac" :: rest => staticAccelerate = true; arguments(rest)
      case "-dynac" :: rest => dynamicAccelerate = true; arguments(rest)
      case "-unap" :: rest => underApproximate = true; arguments(rest)
      case "-tem" :: rest => template = true; arguments(rest)
      case "-dinq" :: rest => dumpInterpolationQuery = true; arguments(rest)
      case "-brew" :: rest => babarew = true; arguments(rest)
      /*      case "-bfs" :: rest => searchMethod = BFS; arguments(rest)
            case "-prq" :: rest => searchMethod = PRQ; arguments(rest)
            case "-dfs" :: rest => searchMethod = DFS; arguments(rest)
            case "-rnd" :: rest => searchMethod = RND; arguments(rest)*/
      case tTimeout :: rest if (tTimeout.startsWith("-t:")) =>
        val time = (java.lang.Float.parseFloat(tTimeout.drop(3)) * 1000).toInt
        timeout = Some(time);
        arguments(rest)
      case mFuncName :: rest if (mFuncName.startsWith("-m:")) => funcName = mFuncName drop 3; arguments(rest)
      case sSolFileName :: rest if (sSolFileName.startsWith("-s:")) => solFileName = sSolFileName.drop(3); arguments(rest)
      case "-log" :: rest => setLogLevel(2); arguments(rest)
      case "-statistics" :: rest => setLogLevel(1); arguments(rest)
      case logOption :: rest if (logOption startsWith "-log:") =>
        setLogLevel((logOption drop 5).toInt); arguments(rest)
      case "-logSimplified" :: rest => printHornSimplified = true; arguments(rest)
      case "-dot" :: str :: rest => dotSpec = true; dotFile = str; arguments(rest)
      case "-pngNo" :: rest => pngNo = true; arguments(rest)
      case "-dotCEX" :: rest => pngNo = false; arguments(rest)
      case "-eogCEX" :: rest => pngNo = false; eogCEX = true; arguments(rest)
      case "-cex" :: rest => plainCEX = true; arguments(rest)
      case "-assert" :: rest => TriCeraParameters.get.assertions = true; arguments(rest)
      case "-h" :: rest => println(greeting + "\n\nUsage: tri [options] file\n\n" +
        "General options:\n" +
        " -h\t\tShow this information\n" +
        " -assert\tEnable assertions in TriCera\n" +
        " -log\t\tDisplay progress and found invariants\n" +
        " -log:n\t\tDisplay progress with verbosity n (currently 0 <= n <= 3)\n" +
        " -statistics\tDisplay statistics (implied by -log)\n" +
        " -t:time\tSet timeout (in seconds)\n" +
        " -cex\t\tShow textual counterexamples\n" +
        " -dotCEX\tOutput counterexample in dot format\n" +
        " -eogCEX\tDisplay counterexample using eog\n" +
        " -m:func\tUse function func as entry point (default: main)\n" +
        "\n" +
        "Horn engine:\n" +
        " -horn\t\tEnable this engine\n" +
        " -p\t\tPretty Print Horn clauses\n" +
        " -sp\t\tPretty print the Horn clauses in SMT-LIB format\n" +
        " -sol\t\tShow solution in Prolog format\n" +
        " -ssol\t\tShow solution in SMT-LIB format\n" +
        " -disj\t\tUse disjunctive interpolation\n" +
        " -stac\t\tStatic acceleration of loops\n" +
        " -lbe\t\tDisable preprocessor (e.g., clause inlining)\n" +
        " -arrayQuans:n\tIntroduce n quantifiers for each array argument (default: 1)\n" +
        " -noSlicing\tDisable slicing of clauses\n" +
        " -hints:f\tRead initial predicates and abstraction templates from a file\n" +
        //          " -glb\t\tUse the global approach to solve Horn clauses (outdated)\n" +
        "\n" +
        //          " -abstract\tUse interpolation abstraction for better interpolants (default)\n" +
        " -abstract:t\tInterp. abstraction: off, manual, term, oct,\n" +
        "            \t                     relEqs (default), relIneqs\n" +
        " -abstractTO:t\tTimeout (s) for abstraction search (default: 2.0)\n" +
        " -abstractPO\tRun with and w/o interpolation abstraction in parallel\n" +
        " -splitClauses\tTurn clause constraints into pure inequalities\n" +

        "\n" +
        "C/C++/TA front-end:\n" +
        " -arithMode:t\tInteger semantics: math (default), ilp32, lp64, llp64\n" +
        " -pIntermediate\tDump Horn clauses encoding concurrent programs\n"
      )
        false
      case fn :: rest => fileName = fn; openInputFile; arguments(rest)
    }

    // Exit early if we showed the help
    if (!arguments(args.toList))
      return

    if (in == null) {
      arguments(List("-h"))
      throw new MainException("no input file given")
      return
    }

    val startTime = System.currentTimeMillis

    timeoutChecker = timeout match {
      case Some(to) => () => {
        if (System.currentTimeMillis - startTime > to.toLong)
          throw TimeoutException
        if (stoppingCond)
          throw StoppedException
      }
      case None => () => {
        if (stoppingCond)
          throw StoppedException
      }
    }

    ap.util.Debug enableAllAssertions lazabs.Main.assertions

    if (princess)
      Prover.setProver(lazabs.prover.TheoremProver.PRINCESS)
    val outStream =
      if (logStat) Console.err else lazabs.horn.bottomup.HornWrapper.NullStream

    Console.withOut(outStream) {
      println(
        "---------------------------- Reading C/C++ file --------------------------------")
    }

    val system =
      CCReader(new java.io.BufferedReader(
        new java.io.FileReader(new java.io.File(fileName))),
        funcName,
        arithMode)

    if (prettyPrint)
      tricera.concurrency.ReaderMain.printClauses(system)

    val smallSystem = system.mergeLocalTransitions

    if (prettyPrint) {
      println
      println("After simplification:")
      tricera.concurrency.ReaderMain.printClauses(smallSystem)
      return
    }

    val result = try {
      Console.withOut(outStream) {
        new tricera.concurrency.VerificationLoop(smallSystem).result
      }
    } catch {
      case TimeoutException => {
        println("timeout")
        throw TimeoutException
      }
      case StoppedException => {
        println("stopped")
        throw StoppedException
      }
    }

    result match {
      case Left(_) =>
        println("SAFE")
      case Right(cex) => {
        println("UNSAFE")
        if (plainCEX) {
          println
          tricera.concurrency.VerificationLoop.prettyPrint(cex)
        }
      }
    }

    return

    //if(drawCFG) {DrawGraph(cfg.transitions.toList,cfg.predicates,absInFile,m); return}

    //    if(timeout.isDefined) Z3Wrapper.setTimeout(timeout)

    /*val rTree = if (!interpolation) MakeRTree(cfg, MakeCFG.getLoops, spuriousness, searchMethod, log)
      else MakeRTreeInterpol(cfg, MakeCFG.getLoops, searchMethod, babarew, dumpInterpolationQuery, dynamicAccelerate, underApproximate, template, log)*/
    //if(drawRTree) DrawG                                                                    raph(rTree, absInFile)

  } catch {
    case TimeoutException | StoppedException =>
    // nothing
    case _: java.lang.OutOfMemoryError =>
      printError("out of memory")
    case _: java.lang.StackOverflowError =>
      printError("stack overflow")
    case t: Exception =>
      t.printStackTrace
      printError(t.getMessage)
  }

  private def printError(message: String): Unit =
    if (message == null)
      println("error")
    else
      println("(error \"" + message.replace("\"", "\"\"\"") + "\")")

}
