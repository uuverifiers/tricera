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

import tricera.concurrency.{CCReader, TriCeraPreprocessor}
import java.io.{FileInputStream, FileNotFoundException}

import lazabs.prover._
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.GlobalParameters
import net.jcazevedo.moultingyaml.YF
import tricera.benchmarking.Benchmarking._

////////////////////////////////////////////////////////////////////////////////

object Main {
  // Exceptions
  class MainException(msg: String) extends Exception(msg)
  object TimeoutException extends MainException("timeout")
  object StoppedException extends MainException("stopped")

  // entry point
  def main(args: Array[String]): Unit = {
    val res = doMain(args, false)
    res match {
      case _ : ExecutionError => throw new MainException(res.toString)
      case e : ExecutionSummary => //println(e)
      case _ => // nothing
    }
  }

  def doMain(args: Array[String], stoppingCond: => Boolean) : ExecutionSummary = {
    val triMain = new Main(args)
    triMain.run(stoppingCond)
  }

  private def printError(message: String): Unit =
    if (message == null)
      println("error")
    else
      println("(error \"" + message.replace("\"", "\"\"\"") + "\")")

}

class Main (args: Array[String]) {
  import Main._
  import tricera.params.TriCeraParameters

  val params = TriCeraParameters.get
  params(args.toList)
  GlobalParameters.parameters.value = params
  import params._

  if (in == null) {
    showHelp
    printError("no input file given")
  }

  private var modelledHeap = false
  private val programTimer = new Timer
  private val preprocessTimer = new Timer

  def run(stoppingCond: => Boolean) : ExecutionSummary = try {
    if (params.showedHelp) // Exit early if we showed the help
      return ExecutionSummary(DidNotExecute)
    programTimer.start()

    // work-around: make the Princess wrapper thread-safe
    lazabs.prover.PrincessWrapper.newWrapper

    timeoutChecker = timeout match {
      case Some(to) => () => {
        if (programTimer.ms > to.toDouble)
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
    import java.io.File

    preprocessTimer.start()
    val ppFileName : String = if (noPP) {
      if(printPP || dumpPP)
        Util.warn("Cannot print or dump preprocessor output due to -noPP")
      fileName // no preprocessing
    } else {
      val preprocessedFile = File.createTempFile("tri-", ".tmp")
      preprocessedFile.deleteOnExit()

      if(logPPLevel > 0)
        Console.withOut(outStream) {
          println("=" * 80 + "\nPreprocessor warnings and errors\n")
        }

      val pp = new TriCeraPreprocessor(fileName,
                                      preprocessedFile.getAbsolutePath,
                                      displayWarnings = logPPLevel == 2,
                                      quiet = logPPLevel == 0)
      if(logPPLevel > 0) Console.withOut(outStream) {
        println("\n\nEnd of preprocessor warnings and errors")
        println("=" * 80)
      }

      if(pp.hasError && logPPLevel > 0)
        Util.warn("The preprocessor (LLVM) reported an error in the" +
          " input file, This might be due to TriCera accepting a non-standard" +
          " subset of the C language, or due to an actual error in the " +
          "input program. You can safely ignore this warning if it is" +
          " the former. You can print preprocessor warnings and errors " +
          "using the -warnPP option.")

      if (printPP) {
        val src = scala.io.Source.fromFile(preprocessedFile)
        println(src.mkString)
        src.close
      }
      if (dumpPP) {
        import java.io.{File, FileInputStream, FileOutputStream}
        val dest = new File(fileName + ".tri")
        new FileOutputStream(dest) getChannel() transferFrom(
          new FileInputStream(preprocessedFile) getChannel, 0, Long.MaxValue)
      }
      //if (res.usesArrays)
      //  return ExecutionSummary(ArrayError, Nil, false, 0, preprocessTimer.s)
        //throw new MainException("C arrays are not supported (yet)")
//      /*else*/ if (res.isUnsupported)
//        return ExecutionSummary(
//          OtherError("Unsupported - detected by preprocessor"),
//            Nil, false,  0, preprocessTimer.s)
        //throw new MainException("Input file has unsupported C features " +
        //  "(e.g. varargs)") // todo: more detail
      preprocessedFile.getAbsolutePath
    }
    preprocessTimer.stop()

    // check if an accompanying .yml file exists (SV-COMP style)
    case class BMOption (language : String, data_model : String)
    case class BMPropertyFile(property_file : String,
                              expected_verdict : Option[Boolean] = None,
                              subproperty : Option[String] = None) {
      def isReachSafety = property_file.contains("unreach-call")
      def isMemSafety = property_file.contains("valid-memsafety")
    }
    case class BenchmarkInfo(format_version : String,
                             input_files : String,
                             properties : List[BMPropertyFile],
                             options : BMOption)
    val bmInfo : Option[BenchmarkInfo] = try {
      import java.nio.file.{Paths, Files}
      val yamlFileName = fileName.replaceAll("\\.[^.]*$", "") + ".yml"
      if (Files.exists(Paths.get(yamlFileName))) {
        // println("Accompanying yaml file found")
        import net.jcazevedo.moultingyaml._
        object BenchmarkYamlProtocol extends DefaultYamlProtocol {
          implicit val propFormat = yamlFormat3(BMPropertyFile)
          implicit val optFormat = yamlFormat2(BMOption)
          implicit val bmInfoFormat = yamlFormat4(BenchmarkInfo)
        }
        import BenchmarkYamlProtocol._
        val src = scala.io.Source.fromFile(yamlFileName)
        val yamlAst = src.mkString.stripMargin.parseYaml
        src.close
        Some(yamlAst.convertTo[BenchmarkInfo])
      } else None
    } catch {
      case _: Throwable => Util.warn(
        "could not parse the accompanying Yaml(.yml) file, ignoring it...")
        None
    }

    val bmTracks : List[(BenchmarkTrack, Option[Boolean])]  = bmInfo match {
      case Some(info) =>
        for (p <- info.properties if p.isMemSafety || p.isReachSafety) yield {
          val track =
            if (p.isReachSafety)
              Reachability
            else //(p.isMemSafety)
              p.subproperty match {
                case Some("valid-free") => MemSafety(Some(ValidFree))
                case Some("valid-deref") => MemSafety(Some(ValidDeref))
                case Some("valid-memtrack") => MemSafety(Some(MemTrack))
                case _ => MemSafety(None)
              }
          (track, p.expected_verdict)
        }
      case None => Nil
    }

    if (bmInfo.nonEmpty && bmTracks.isEmpty) {
      return ExecutionSummary(DidNotExecute, preprocessTime = preprocessTimer.s)
      //throw new MainException("An associated property file (.yml) is " +
      //  "found, however TriCera currently can only check for unreach-call" +
      //  " and a subset of valid-memsafety properties.")
    }

    if (bmTracks.exists(t => t._1 match {
      case MemSafety(Some(MemTrack)) => true
      case _  => false
    })) shouldTrackMemory = true
    // todo: pass string to TriCera instead of writing to and passing file?

    // todo: add a switch for this, also benchmark/profile
    val bufferedReader = parsers.CommentPreprocessor(new java.io.BufferedReader(
      new java.io.FileReader(new java.io.File(ppFileName))))
    val (reader, modelledHeapRes) =
      CCReader(bufferedReader, funcName, arithMode, shouldTrackMemory)

    import tricera.acsl.Encoder
    val enc : Encoder = new Encoder(reader, reader.annotFunctionContracts)
    val system = enc.encode

    val systemPostProcessors = Seq()

    // todo: generate new system here by substituting pre-/post-conditions


    modelledHeap = modelledHeapRes

    if (prettyPrint) {
      tricera.concurrency.ReaderMain.printClauses(system)
    }

    val smallSystem = system.mergeLocalTransitions

    if (prettyPrint) {
      println
      println("After simplification:")
      tricera.concurrency.ReaderMain.printClauses(smallSystem)
      return ExecutionSummary(DidNotExecute, Nil, modelledHeap, 0, preprocessTimer.s)
    }

    if(smtPrettyPrint) {
      tricera.concurrency.ReaderMain.printSMTClauses(smallSystem)
      return ExecutionSummary(DidNotExecute, Nil, modelledHeap, 0, preprocessTimer.s)
    }

    val expectedStatus =
      // sat if no tracks are false, unsat otherwise
      if (bmTracks.nonEmpty) {
        if (bmTracks.forall { track => !track._2.contains(false) }) "sat"
        else "unsat"
      } else "unknown"

    val result = try {
      Console.withOut(outStream) {
        new hornconcurrency.VerificationLoop(smallSystem, null,
          printIntermediateClauseSets, fileName + ".smt2",
          expectedStatus = expectedStatus, log = log,
          templateBasedInterpolation =  templateBasedInterpolation,
          templateBasedInterpolationTimeout = templateBasedInterpolationTimeout)
          .result
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

    val executionResult = result match {
      case Left(res) =>
        println("SAFE")
        res match {
          case Some(solution) =>
            import ap.parser.ITerm
            import tricera.concurrency.ACSLLineariser
            import reader.CCPredicate

            def replaceArgs(p : CCPredicate, f : String) = {
              var s = f
              for (ind <- (p.arity - 1) to 0 by - 1) {
                val actualArg : String = {
                  if (p.oldVars contains ind)
                    "\\old(" + p.argVars(ind) + ")"
                  else if (p.resVarInd == ind)
                    "\\result"
                  else p.argVars(ind).toString
                }
                s = s.replace("_" + ind, actualArg)
              }
              s
            }

            val contracts = reader.getFunctionContracts
            for ((fun, (pre, post)) <- contracts) {
              val fPre  = ACSLLineariser asString solution(pre.pred)
              val fPost = ACSLLineariser asString solution(post.pred)

              val fPreWithArgs  = replaceArgs(pre,  fPre)
              val fPostWithArgs = replaceArgs(post, fPost)

              println("/* contracts for " + fun + " */")
              println("/*@")
              print  ("  requires ") ; println(fPreWithArgs + ";")
              print  ("  ensures ")  ; println(fPostWithArgs + ";")
              println("*/")
            }

            /*if(system.backgroundPreds.exists(p => p.name.contains("_pre"))) {
              println("Contracts:")
              for (p <- system.backgroundPreds) if (p.name.contains("_pre") ||
                p.name.contains("_post")) {

                if(p.name.contains("_pre")){
                  system.backgroundAxioms.clauses.find(c =>
                    c.body.exists(a => a.pred == p)) match {
                    case None =>
                    case Some(pre) =>
                      val args =
                        pre.body.find(c => c.pred == p) match {
                          case Some(a) => a.args
                          case None => throw new Exception("cannot find f_pre")
                        }
                      printFun(args)
                  }
                } else { //post
                  system.backgroundAxioms.clauses.find(c => c.head.pred == p)
                  match {
                    case None =>
                    case Some(post) => printFun(post.head.args)
                  }
                }
              }
              println
            }*/
          case None =>
        }
        Safe
      case Right(cex) => {
        println("UNSAFE")
        if (plainCEX) {
          println
          //reader.printPredsWithArgNames
          hornconcurrency.VerificationLoop.prettyPrint(cex)
        }
        Unsafe
      }
    }

    def getExpectedVerdict (expected : Option[Boolean]) : Boolean =
      expected match {
        case Some(verdict) => verdict
        case None => throw new MainException("Benchmark information provided" +
          "with no expected verdict!")
      }
    def printVerdictComparison(comparison : Boolean) : Unit =
      if (comparison) println("  expected verdict matches the result!")
      else println("  expected verdict mismatch!")

    val trackResult = for (track <- bmTracks) yield {
      println(track._1)
      val expectedVerdict = getExpectedVerdict(track._2)
      val verdictMatches =  expectedVerdict == result.isLeft
      printVerdictComparison(verdictMatches)
      (track._1, expectedVerdict)
    }

    ExecutionSummary(executionResult, trackResult, modelledHeap,
      programTimer.s, preprocessTimer.s)

    //if(drawCFG) {DrawGraph(cfg.transitions.toList,cfg.predicates,absInFile,m); return}

    //    if(timeout.isDefined) Z3Wrapper.setTimeout(timeout)

    /*val rTree = if (!interpolation) MakeRTree(cfg, MakeCFG.getLoops, spuriousness, searchMethod, log)
      else MakeRTreeInterpol(cfg, MakeCFG.getLoops, searchMethod, babarew, dumpInterpolationQuery, dynamicAccelerate, underApproximate, template, log)*/
    //if(drawRTree) DrawG                                                                    raph(rTree, absInFile)

  } catch {
    case TimeoutException | StoppedException =>
      ExecutionSummary(Timeout, Nil, modelledHeap,
        programTimer.s, preprocessTimer.s)
    // nothing
    case _: java.lang.OutOfMemoryError =>
      printError(OutOfMemory.toString)
      ExecutionSummary(OutOfMemory, Nil, modelledHeap,
        programTimer.s, preprocessTimer.s)
    case _: java.lang.StackOverflowError =>
      printError(StackOverflow.toString)
      ExecutionSummary(StackOverflow, Nil, modelledHeap,
        programTimer.s, preprocessTimer.s)
    case e: CCReader.ArrayException =>
      //e.printStackTrace()
      printError(ArrayError.toString)
      ExecutionSummary(ArrayError, Nil, modelledHeap)
    case t: Exception =>
      t.printStackTrace
      printError(t.getMessage)
      ExecutionSummary(OtherError(t.getMessage), Nil, modelledHeap,
        programTimer.s, preprocessTimer.s)
    case t: AssertionError =>
      printError(t.getMessage)
      t.printStackTrace
      ExecutionSummary(OtherError(t.getMessage), Nil, modelledHeap,
        programTimer.s, preprocessTimer.s )
  }

}
