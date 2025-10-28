/**
  * Copyright (c) 2011-2025 Zafer Esen, Hossein Hojjat, Philipp Ruemmer.
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

import java.io.{FileOutputStream, PrintStream}
import java.nio.file.{Files, Paths}
import sys.process._
import ap.parser.IExpression.{ConstantTerm, Predicate}
import ap.parser.{IAtom, IConstant, IFormula, VariableSubstVisitor}
import hornconcurrency.ParametricEncoder
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.Util.NullStream
import lazabs.prover._
import tricera.concurrency.{CCReader, TriCeraPreprocessor}
import tricera.Util.{SourceInfo, printlnDebug}
import tricera.benchmarking.Benchmarking._
import tricera.concurrency.CCReader.{CCAssertionClause, CCClause}
import tricera.concurrency.ccreader.CCExceptions._
import tricera.concurrency.ccreader.{CCHeapArrayPointer, CCHeapPointer, CCStackPointer, CCVar}
import lazabs.horn.preprocessor.HornPreprocessor
import tricera.postprocessor.FunctionInvariantsFilter
import tricera.postprocessor.ACSLLinearisedContract
import tricera.concurrency.CallSiteTransform.CallSiteTransforms
import tricera.postprocessor.MergeTransformedFunctionsContracts
import tricera.postprocessor.AddValidPointerPredicates

import java.util.concurrent.ExecutionException

////////////////////////////////////////////////////////////////////////////////

object Main {
  // Exceptions
  class MainException(msg: String) extends Exception(msg)
  object TimeoutException extends MainException("timeout")
  object StoppedException extends MainException("stopped")

  // entry point
  def main(args: Array[String]): Unit = {
    val res = doMain(args, false)
    res.executionResult match {
      case _ : ExecutionError   => throw new MainException(res.toString)
      case _ =>
    }
  }

  def doMain(args: Array[String], stoppingCond: => Boolean) : ExecutionSummary = {
    val triMain = new Main(args)

    triMain.programTimer.start()
    var remainingTimeout : Option[Int] = params.TriCeraParameters.get.timeout

    val (propertiesToCheck, propertyToExpected) = collectProperties

    /**
     * @todo Below implementation can be improved a lot - there is no
     *       need for the reader to parse the input for each property.
     */
    val result = if (tricera.params.TriCeraParameters.get.splitProperties &&
                     propertiesToCheck.size > 1) {
      println(s"Splitting properties: {${propertiesToCheck.mkString(",")}}")
      var remainingProperties = propertiesToCheck
      var overallResult = ExecutionSummary(DidNotExecute)

      var prevDuration = triMain.programTimer.s
      while(remainingProperties nonEmpty) {
        val property = remainingProperties.head
        print(s"  $property... ")
        remainingProperties = remainingProperties.tail

        remainingTimeout = remainingTimeout match {
          case Some(to) => Some((to.toDouble - triMain.programTimer.ms).toInt)
          case None => None
        }
        val propertyResult =
          triMain.run(stoppingCond, Set(property), propertyToExpected,
                      remainingTimeout)
        val runDuration = propertyResult.elapsedTime - prevDuration
        prevDuration = propertyResult.elapsedTime
        if (propertyResult.executionResult != DidNotExecute) {
          overallResult = ExecutionSummary(
            propertyResult.executionResult,
            overallResult.propertyResult ++ propertyResult.propertyResult,
            overallResult.modelledHeap || propertyResult.modelledHeap,
            propertyResult.elapsedTime, // this accumulates between runs
            overallResult.preprocessTime + propertyResult.preprocessTime)
          if (propertyResult.executionResult != Safe &&
              propertyResult.executionResult != DidNotExecute) {
            // No need to continue if we could not prove this property.
            remainingProperties = Set()
          }
          println(propertyResult.executionResult)
        }
      }
      overallResult
    } else {
      triMain.run(stoppingCond, propertiesToCheck, propertyToExpected,
                  remainingTimeout)
    }
    println(result.executionResult)
    result
  }

  private def collectProperties : (Set[properties.Property],
                                   Map[properties.Property, Boolean]) = {
    val params = tricera.params.TriCeraParameters.get
    import params._
    import tricera.parsers.YAMLParser._
    // Check if an accompanying .yml file exists (SV-COMP style).
    val yamlFileName = fileName.replaceAll("\\.[^.]*$", "") + ".yml"
    val bmInfo : Option[BenchmarkInfo] =
      if (Files.exists(Paths.get(yamlFileName))) {
        val info = extractBenchmarkInfo(yamlFileName)
        if (info isEmpty) Util.warn(
          "Could not parse the accompanying YAML (.yml) file, ignoring it.")
        info
      } else None

    /**
     * Properties to check and their expected status, if any.
     */
    val (propertiesToCheck : Set[properties.Property],
         propertyToExpected : Map[properties.Property, Boolean]) = {
      val cliProps : Set[properties.Property] = Set(
        if (checkMemTrack) Some(properties.MemValidTrack) else None,
        if (checkValidFree) Some(properties.MemValidFree) else None,
        if (checkValidDeref) Some(properties.MemValidDeref) else None,
        if (checkMemCleanup) Some(properties.MemValidCleanup) else None,
        if (checkReachSafety) Some(properties.Reachability) else None).flatten ++
        (if (checkMemSafety)
           memSafetyProperties else Set[properties.Property]())

      if (cliProps.nonEmpty && bmInfo.nonEmpty) {
        Util.warn("A property file exists, but properties are also " +
                  "specified in the command-line. Ignoring the property file.")
        (cliProps, Map.empty[properties.Property, Boolean])
      } else if (bmInfo.nonEmpty) {
        // SV-COMP style property specification.
        val props = bmInfo.get.properties.flatMap{p =>
          val verdictOption = p.expected_verdict
          p match {
            case _ if p.isReachSafety =>
              verdictOption.map(properties.Reachability -> _)

            case _ if p.isMemSafety  =>
              val initialSubProps = memSafetyProperties.map(_ -> true).toMap
              // At most one sub-property is expected to not hold, if any.
              val updatedSubProps = verdictOption match {
                case Some(false) => p.subproperty match {
                  case Some("valid-free") =>
                    initialSubProps.updated(properties.MemValidFree, false)
                  case Some("valid-deref") =>
                    initialSubProps.updated(properties.MemValidDeref, false)
                  case Some("valid-memtrack") =>
                    initialSubProps.updated(properties.MemValidTrack, false)
                  case Some(prop) => throw new Exception(
                    s"Unknown sub-property $prop for the memsafety category.")
                  case None => throw new Exception(
                    "For memsafety where the expected verdict is 'false', the " +
                    "failing sub-property must be specified. Alternatively, the " +
                    "expected verdict can be removed.")
                }
                case _ => initialSubProps
              }
              updatedSubProps
            case _ if p.isMemCleanup =>
              verdictOption.map(properties.MemValidCleanup -> _)

            case _ => None
          }
        }.toMap

        val propsSet : Set[properties.Property] = props.keys.toSet
        (propsSet, props)
      } else {
        // No property file: use CLI properties. If none, use Reachability.
        (if (cliProps nonEmpty) cliProps else Set(properties.Reachability),
          Map[properties.Property, Boolean]())
      }
    }
    (propertiesToCheck, propertyToExpected)
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
  lazabs.GlobalParameters.parameters.value = params
  import params._

  if (in == null && !params.doNotExecute) {
    showHelp
    printError("no input file given")
  }

  private var modelledHeap = false
  private val programTimer = new Timer
  private val preprocessTimer = new Timer

  def run(stoppingCond: => Boolean,
          propertiesToCheck : Set[properties.Property],
          propertyToExpected : Map[properties.Property, Boolean],
          runTimeout : Option[Int])
  : ExecutionSummary = try {
    if (params.doNotExecute) // Exit early if we showed the help
      return ExecutionSummary(DidNotExecute)

    // work-around: make the Princess wrapper thread-safe
    lazabs.prover.PrincessWrapper.newWrapper

    timeoutChecker = runTimeout match {
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
      if (logStat || printHornSimplified || printHornSimplifiedSMT)
        Console.err
      else
        NullStream

    Console.withOut(outStream) {
      println(
        "---------------------------- Reading C/C++ file --------------------------------")
    }
    import java.io.File

    // C preprocessor (cpp)
    val cppFileName =
      if(params.cPreprocessor)
        CPreprocessor(fileName, includeSystemHeaders = true, params.arithMode)
      else fileName

    // TriCera preprocessor (tri-pp)
    preprocessTimer.start()
    val ppFileName: String = if (noPP) {
      if (printPP || dumpPP)
        Util.warn("Cannot print or dump preprocessor output due to -noPP")
      cppFileName // no preprocessing
    } else {
      val preprocessedFile = File.createTempFile("tri-", ".tmp")
      preprocessedFile.deleteOnExit()

      if (logPPLevel > 0)
        Console.withOut(outStream) {
          println("=" * 80 + "\nTriCera's preprocessor (tri-pp) warnings and errors\n")
        }

      val pp = new TriCeraPreprocessor(cppFileName,
        preprocessedFile.getAbsolutePath,
        displayWarnings = logPPLevel == 2,
        quiet = logPPLevel == 0,
        entryFunction = TriCeraParameters.get.funcName)
      if (logPPLevel > 0) Console.withOut(outStream) {
        println("\n\nEnd of TriCera's preprocessor (tri-pp) warnings and errors")
        println("=" * 80)
      }

      if (pp.hasError && logPPLevel > 0)
        Util.warn(
          """The preprocessor tri-pp (LLVM) reported an error in the input file, This might
            |be due to TriCera accepting a non-standard subset of the C language, or
            |due to an actual error in the input program. You can safely ignore this
            |warning if it is the former.""".stripMargin)

      if (printPP) {
        val src = scala.io.Source.fromFile(preprocessedFile)
        println(src.mkString)
        src.close
      }
      if (dumpPP) {
        import java.io.{File, FileInputStream, FileOutputStream}
        val dest = new File(fileName + ".tri")
        new FileOutputStream(dest).getChannel transferFrom(
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
      if(preprocessedFile.length() == 0 && pp.hasError) {
        Util.warn(
          """TriCera preprocessor (tri-pp) returned an empty file - attempting
            |to continue without it. Use option -logPP:2 to display what went
            |wrong, use option -noPP to disable the preprocessor and this warning.
            |""".stripMargin)
        cppFileName
      } else {
        preprocessedFile.getAbsolutePath
      }
    }
    preprocessTimer.stop()

    Console.withOut(outStream){
      println("Checked properties:")
      for (prop <- propertiesToCheck) {
        print(s"  $prop")
        propertyToExpected get prop match {
          case Some(expected) => println(s" (expected: $expected)")
          case None           => println
        }
      }
      println
    }

    // todo: pass string to TriCera instead of writing to and passing file?

    // todo: add a switch for this, also benchmark/profile
    val bufferedReader = parsers.CommentPreprocessor(new java.io.BufferedReader(
      new java.io.FileReader(new java.io.File(ppFileName))))
    val (reader, modelledHeapRes, callSiteTransforms) =
      try {
        CCReader(bufferedReader, funcName, propertiesToCheck)
      } catch {
        case e : ParseException if !devMode =>
          return ExecutionSummary(ParseError(e.getMessage), Map(),
                                  modelledHeap, 0, preprocessTimer.s)
        case e : TranslationException if !devMode =>
          return ExecutionSummary(TranslationError(e.getMessage), Map(),
                                  modelledHeap, 0, preprocessTimer.s)
        case e : UnsupportedCastException =>
          return ExecutionSummary(Unknown(e.getMessage), Map(),
                                  modelledHeap, 0, preprocessTimer.s)
        case e : UnsupportedCFragmentException =>
          return ExecutionSummary(
            Unknown("Unsupported C fragment. " + e.getMessage), Map(),
            modelledHeap, 0, preprocessTimer.s)
        case e : Throwable => throw e
      }

    import tricera.acsl.Encoder

    val (system, maybeEnc : Option[Encoder]) = if (reader.funToContract.nonEmpty) {
      val enc = new Encoder(reader)
      (enc.encode, Some(enc))
    } else (reader.system, None)

    def checkForSameNamedTerms = {
      val clausesWithSameNamedTerms =
        (system.processes.flatMap(_._1).map(_._1) ++ system.assertions).filter(
          c => c.constants.size != c.constants.map(_.name).size)
      for (c <- clausesWithSameNamedTerms) {
        import ap.parser.{IBinJunctor, LineariseVisitor, Transform2NNF}
        import ap.parser.IExpression._
        val sameNamedTerms =
          c.constants.groupBy(_.name).filter{
            case (name, constants) => constants.size > 1 && name != "_"
          }
        val conjuncts =
          LineariseVisitor(Transform2NNF(c.constraint), IBinJunctor.And)

        val possibleEqualityFormulas =
          for ((_, terms) <- sameNamedTerms) yield {
            val termEqualityFormulas =
              terms.toSeq.combinations(2).flatMap(ts =>
                scala.Seq(ts(0) === ts(1), ts(1) === ts(0))).toSeq
            termEqualityFormulas
          }

        val sameTermFormulasThatAreNotEqual = possibleEqualityFormulas.filter(f =>
          f.forall(eq => !conjuncts.contains(eq)))

        for (f <- sameTermFormulasThatAreNotEqual) {
          f.head match {
            case Eq(ap.parser.IConstant(t), _) =>
              Util.warn("The following clause has different terms with the same " +
                "name (term: " + t.name + ")\n" + c.toPrologString + "\n")
            case _ => // should not be possible
          }
        }
      }
    }
    if(devMode) // todo: make part of -assert?
      checkForSameNamedTerms

    modelledHeap = modelledHeapRes

    if (prettyPrint) {
      val clauseToSrcInfo : Map[Clause, Option[SourceInfo]] =
      (system.processes.flatMap(_._1.map(_._1)) ++
        system.assertions).map(reader.getRichClause).filter(_.nonEmpty).map(c =>
        (c.get.clause, c.get.srcInfo)).toMap
      tricera.concurrency.ReaderMain.printClauses(system, reader.PredPrintContext, clauseToSrcInfo)
    }

    val (smallSystem, mergedToOriginal) = system.mergeLocalTransitionsWithBackMapping

//    mergedToOriginal.foreach{
//      case (c, cs) =>
//        println(c.toPrologString)
//        cs.foreach(origC => println("  " + origC.toPrologString))
//        println("-"*80)
//    }

    if (prettyPrint) {
      println
      println("After simplification:")
      tricera.concurrency.ReaderMain.printClauses(smallSystem, reader.PredPrintContext, Map())
    }

    if(smtPrettyPrint)
      tricera.concurrency.ReaderMain.printSMTClauses(smallSystem)

    if(prettyPrint || smtPrettyPrint)
      return ExecutionSummary(DidNotExecute, Map(), modelledHeap, 0, preprocessTimer.s)

    /**
     * Expected status is printed in SMT files when they are dumped.
     */
    val expectedStatus =
      // sat if no properties are expected to be false, unsat otherwise
      if (propertiesToCheck.forall(propertyToExpected.contains)) {
        if (propertyToExpected.filter(
          pair => propertiesToCheck.contains(pair._1)).forall(_._2)) {
          if (useMemCleanupForMemTrack &&
              propertiesToCheck.contains(properties.MemValidTrack)) {
            /**
             *  memtrack expected is 'sat', but TriCera encodes the stronger
             *  property valid-cleanup, which might be 'unsat'.
             */
            "unknown"
          } else "sat"
        }
        else "unsat"
      } else "unknown"

    val smtFileName = if (splitProperties) {
      assert(propertiesToCheck.size == 1)
      s"$fileName-${propertiesToCheck.head}.smt2"
    } else {
      s"$fileName.smt2"
    }

    val verificationLoop =
      try {
        Console.withOut(outStream) {
          new hornconcurrency.VerificationLoop(
            system = smallSystem,
            initialInvariants = null,
            dumpIntermediateClauses = printIntermediateClauseSets,
            dumpSimplifiedClauses = dumpSimplifiedClauses,
            fileName = smtFileName,
            expectedStatus = expectedStatus,
            log = needFullSolution,
            templateBasedInterpolation = templateBasedInterpolation,
            templateBasedInterpolationTimeout = templateBasedInterpolationTimeout,
            symbolicExecutionEngine = symexEngine,
            symbolicExecutionDepth = symexMaxDepth,
            logSymbolicExecution = log
          )
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

    if (printIntermediateClauseSets || dumpSimplifiedClauses ||
        printHornSimplified || printHornSimplifiedSMT)
      return ExecutionSummary(DidNotExecute, Map(), modelledHeap, 0, preprocessTimer.s)

    import tricera.Util._
    import tricera.postprocessor.ResultPrinters.{printSolutionProlog, printSolutionSMT}
    import tricera.postprocessor.ResultConverter.hornSolverSolutionToResult

    val result = verificationLoop.result
      .tapIf(displaySolutionProlog)(printSolutionProlog(reader.PredPrintContext.predArgNames))
      .tapIf(lazabs.GlobalParameters.get.displaySolutionSMT)(printSolutionSMT)
      .through(hornSolverSolutionToResult(reader, TriCeraParameters.get.funcName))
      .through(MergeTransformedFunctionsContracts(callSiteTransforms))

    val executionResult = result match {
      case solution: Solution => 
        import tricera.postprocessor._
        import tricera.postprocessor.PointerTools._

        if ((displayACSL || log) &&
          (solution.hasFunctionInvariants || solution.hasLoopInvariants)) {
          result
            .through(FunctionInvariantsFilter(i => !i.isSrcAnnotated)(_))
            .through(ADTExploder.apply)
            .through(PostconditionSimplifier.apply)
            .through(r =>
              if (solution.isHeapUsed) { r
                 .through(addPointerPredicatesFrom(r))
                 .through(addPointerAssignmentsFrom(r))
                 .through(ADTExploder.apply)
                 .through(TheoryOfHeapProcessor.apply)
                 .through(ADTSimplifier.apply) // Rewrite constructors/selectors after heap processing
                 .through(ToVariableForm.apply)
              } else {
                r
              }
            )
            .tap(r => r
              .through(ACSLExpressionProcessor.apply)
              .through(ClauseRemover.apply)
              .through(RewrapPointers.apply)
              .through(AddValidPointerPredicates.apply)
              .through(FormulaSimplifier.apply)
              .through(ACSLLineariser.apply)
              .through(ResultPrinters.printACSL) 
            ).ignore
        }
        Safe
      case _: Empty =>
        Safe
      case CounterExample(cex) => {
        val clauseToUnmergedRichClauses : Map[Clause, scala.Seq[CCClause]] = cex._2.iterator.map {
          case (_, clause) =>
            val richClauses : scala.Seq[CCClause] = mergedToOriginal get clause
            match {
              case Some(clauses) =>
                for (Some(richClause) <- clauses map reader.getRichClause) yield
                  richClause
              case None =>
                reader.getRichClause(clause) match {
                  case None => Nil
                  case Some(richClause) => scala.Seq(richClause)
                }
            }
            (clause -> richClauses)
        }.toMap

        val violatedAssertionClause     = cex._2.head._2
        val violatedRichAssertionClause =
          clauseToUnmergedRichClauses get violatedAssertionClause match {
            case Some(richClauses) if richClauses != Nil =>
              assert(richClauses.size == 1)
              Some(richClauses.head.asInstanceOf[CCAssertionClause])
            case _                                       => None
          }

        if (plainCEX) {
          if (cex._1 == Nil) { // todo: print cex when hornConcurrency no
            // longer returns Nil
            println("This counterexample cannot be printed in the " +
                    "console, use -eogCEX for a graphical view.")
          }
          else {
            println
            hornconcurrency.VerificationLoop.prettyPrint(cex)
            if (system.processes.size == 1 &&
                system.processes.head._2 == ParametricEncoder.Singleton) { //
              // todo: print failed assertion for concurrent systems
              violatedRichAssertionClause match {
                case Some(assertionClause) =>
                  println("Failed assertion:\n" + assertionClause.toString)
                  println
                case None                  =>
              }
            }
          }
        }
        if (!pngNo) { // dotCEX and maybe eogCEX
          if (system.processes.size == 1 &&
              system.processes.head._2 == ParametricEncoder.Singleton) {
            Util.show(cex._2, "cex",
                      clauseToUnmergedRichClauses.map(c => (c._1 ->
                                                            c._2.filter(_.srcInfo.nonEmpty).map(_.srcInfo.get))),
                      reader.PredPrintContext.predArgNames,
                      reader.PredPrintContext.predSrcInfo,
                      reader.PredPrintContext.isUninterpretedPredicate)
          } else {
            println("Cannot display -eogCEX for concurrent processes, try " +
                    "-cex.")
          }
        }
        if (propertiesToCheck.contains(properties.MemValidTrack)
            && params.useMemCleanupForMemTrack) {
          if (system.processes.length > 1) {
            println("Checking memtrack property with more than one process is" +
                    " not supported.")
            Unknown("concurrency - cannot check memtrack")
          } else if (violatedRichAssertionClause.nonEmpty &&
                     violatedRichAssertionClause.get.property ==
                     properties.MemValidCleanup) {
            /**
             * The stronger property valid-memcleanup was violated, we cannot
             * conclude that the weaker valid-memtrack is also violated.
             */
            Unknown("memcleanup violated - memtrack inconclusive")
          } else Unsafe
        } else Unsafe
      }
    }

    def printVerdictComparison(comparison : Boolean) : Unit =
      if (comparison) println("  expected verdict matches the result.")
      else println("  expected verdict mismatch.")

    val trackResult = for ((prop, expected) <- propertyToExpected) yield {
//      println(prop)
      val verdictMatches =  expected == result.isSolution
//      printVerdictComparison(verdictMatches)
      (prop, verdictMatches)
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
      ExecutionSummary(Timeout, Map(), modelledHeap,
        programTimer.s, preprocessTimer.s)
    // nothing
    case _: java.lang.OutOfMemoryError =>
      printError(OutOfMemory.toString)
      ExecutionSummary(OutOfMemory, Map(), modelledHeap,
        programTimer.s, preprocessTimer.s)
    case t: java.lang.StackOverflowError =>
      if(devMode)
        t.printStackTrace
      printError(StackOverflow.toString)
      ExecutionSummary(StackOverflow, Map(), modelledHeap,
        programTimer.s, preprocessTimer.s)
    case t: Exception =>
      if(devMode)
        t.printStackTrace
      printError(t.getMessage)
      ExecutionSummary(OtherError(t.getMessage), Map(), modelledHeap,
        programTimer.s, preprocessTimer.s)
    case t: AssertionError =>
      printError(t.getMessage)
      if(devMode)
        t.printStackTrace
      ExecutionSummary(OtherError(t.getMessage), Map(), modelledHeap,
        programTimer.s, preprocessTimer.s )
  }

}
