/**
  * Copyright (c) 2011-2023 Zafer Esen, Hossein Hojjat, Philipp Ruemmer.
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

import hornconcurrency.ParametricEncoder

import java.io.{FileOutputStream, PrintStream}
import lazabs.horn.bottomup.HornClauses.Clause
import tricera.concurrency.{CCReader, TriCeraPreprocessor}
import lazabs.prover._
import tricera.Util.{SourceInfo, printlnDebug}
import tricera.benchmarking.Benchmarking._
import tricera.concurrency.CCReader.CCClause
import tricera.concurrency.ccreader.CCExceptions._

import sys.process._

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
    val res = triMain.run(stoppingCond)
    res.executionResult match {
      case Safe   => // nothing, already printed
      case Unsafe => // nothing, already printed
      case other  => println(other)
    }
    res
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

  def run(stoppingCond: => Boolean) : ExecutionSummary = try {
    if (params.doNotExecute) // Exit early if we showed the help
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

    val cppFileName = if (cPreprocessor) {
      val preprocessedFile = File.createTempFile("tri-", ".i")
      System.setOut(new PrintStream(new FileOutputStream(preprocessedFile)))
      val cmdLine = "cpp " + fileName + " -E -P -CC"
      try {
        cmdLine !
      }
      catch {
        case _: Throwable =>
          throw new Main.MainException("The preprocessor could not" +
            " be executed. This might be due to TriCera preprocessor binary " +
            "not being in the current directory. Alternatively, use the " +
            "-noPP switch to disable the preprocessor.\n" +
            "Preprocessor command: " + cmdLine
          )
      }
      preprocessedFile.deleteOnExit()
      preprocessedFile.getAbsolutePath
    } else fileName

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
          println("=" * 80 + "\nPreprocessor warnings and errors\n")
        }

      val pp = new TriCeraPreprocessor(cppFileName,
        preprocessedFile.getAbsolutePath,
        displayWarnings = logPPLevel == 2,
        quiet = logPPLevel == 0,
        entryFunction = TriCeraParameters.get.funcName)
      if (logPPLevel > 0) Console.withOut(outStream) {
        println("\n\nEnd of preprocessor warnings and errors")
        println("=" * 80)
      }

      if (pp.hasError && logPPLevel > 0)
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
    case class BMOption(language: String, data_model: String)
    case class BMPropertyFile(property_file: String,
                              expected_verdict: Option[Boolean] = None,
                              subproperty: Option[String] = None) {
      def isReachSafety = property_file.contains("unreach-call")

      def isMemSafety = property_file.contains("valid-memsafety")
    }
    case class BenchmarkInfo(format_version: String,
                             input_files: String,
                             properties: List[BMPropertyFile],
                             options: BMOption)
    val bmInfo: Option[BenchmarkInfo] = try {
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

    val bmTracks: List[(BenchmarkTrack, Option[Boolean])] = bmInfo match {
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
      case MemSafety(Some(ValidFree)) => true
      case _ => false
    })) shouldTrackMemory = true
    // todo: pass string to TriCera instead of writing to and passing file?

    // todo: add a switch for this, also benchmark/profile
    val bufferedReader = parsers.CommentPreprocessor(new java.io.BufferedReader(
      new java.io.FileReader(new java.io.File(ppFileName))))
    val (reader, modelledHeapRes) =
      try {
        CCReader(bufferedReader, funcName, shouldTrackMemory)
      } catch {
        case e: ParseException if !devMode =>
          return ExecutionSummary(ParseError(e.getMessage), Nil, modelledHeap, 0, preprocessTimer.s)
        case e: TranslationException if !devMode =>
          return ExecutionSummary(TranslationError(e.getMessage), Nil, modelledHeap, 0, preprocessTimer.s)
        case e: Throwable => throw e
      }

    if (printPathConstraints) {
      import lazabs.horn.bottomup.HornClauses._
      import ap.parser._

      val clauses : Seq[Clause] = reader.system.processes.flatMap(_._1.map(_._1))
      val predPathConstraints = symex.PathConstraints(clauses)
      val entryFun = TriCeraParameters.get.funcName
      println
      val exitPred =
        reader.PredPrintContext.getFunctionExitPred(entryFun).get.pred
      println("Path constraints for " + entryFun + ":")
      predPathConstraints(exitPred).foreach(c =>
        if(!c.isFalse)
          println(PrincessLineariser.asString(c)))
      println
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
          c.constants.groupBy(_.name).filter(_._2.size > 1)
        val conjuncts =
          LineariseVisitor(Transform2NNF(c.constraint), IBinJunctor.And)

        val possibleEqualityFormulas =
          for ((_, terms) <- sameNamedTerms) yield {
            val termEqualityFormulas =
              terms.toSeq.combinations(2).flatMap(ts =>
                Seq(ts(0) === ts(1), ts(1) === ts(0))).toSeq
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

    if(prettyPrint || smtPrettyPrint || printPathConstraints)
      return ExecutionSummary(DidNotExecute, Nil, modelledHeap, 0, preprocessTimer.s)

    val expectedStatus =
      // sat if no tracks are false, unsat otherwise
      if (bmTracks.nonEmpty) {
        if (bmTracks.forall { track => !track._2.contains(false) }) "sat"
        else "unsat"
      } else "unknown"

    val verificationLoop =
      try {
        Console.withOut(outStream) {
          new hornconcurrency.VerificationLoop(smallSystem, null,
            printIntermediateClauseSets, fileName + ".smt2",
            expectedStatus = expectedStatus, log = needFullSolution,
            templateBasedInterpolation = templateBasedInterpolation,
            templateBasedInterpolationTimeout = templateBasedInterpolationTimeout)
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

    val result = verificationLoop.result

    if (printIntermediateClauseSets)
      return ExecutionSummary(DidNotExecute, Nil, modelledHeap, 0, preprocessTimer.s)

    val executionResult = result match {
      case Left(res) =>
        println("SAFE")
        res match {
          case Some(solution) =>
            import tricera.postprocessor._
            import lazabs.horn.global._
            import lazabs.horn.bottomup.HornPredAbs
            import lazabs.ast.ASTree.Parameter

            def replaceArgs(f : String,
                            acslArgNames : Seq[String],
                            replaceAlphabetic : Boolean = false) = {
              var s = f
              for ((acslArg, ind)<- acslArgNames zipWithIndex) {
                val replaceArg =
                  if (replaceAlphabetic)
                    lazabs.viewer.HornPrinter.getAlphabeticChar(ind)
                  else "_" + ind
                s = s.replace(replaceArg, acslArg)
              }
              s
            }

            if(displaySolutionProlog) {
              // todo: replace args with actual ones from the clauses
              println("\nSolution (Prolog)")
              println("="*80)
              val sortedSol = solution.toArray.sortWith(_._1.name < _._1.name)
              for((pred,sol) <- sortedSol) {
                val cl = HornClause(RelVar(pred.name.stripPrefix("inv_"),
                  (0 until pred.arity).map(p =>
                    Parameter("_" + p,lazabs.types.IntegerType())).toList),
                  List(Interp(lazabs.prover.PrincessWrapper.formula2Eldarica(sol,
                    Map[ap.terfor.ConstantTerm,String]().empty,false))))
                println(replaceArgs(lazabs.viewer.HornPrinter.print(cl),
                                    reader.PredPrintContext.predArgNames(pred),
                                    replaceAlphabetic = true))
              }
              println("="*80 + "\n")
            }
            if (lazabs.GlobalParameters.get.displaySolutionSMT) {
              // TODO: this should probably just use the function for printing
              // models in SMTLineariser. But will change the syntax a bit
              // and require tests to be updated

              // todo: replace args with actual ones from the clauses
              println("\nSolution (SMT-LIB)")
              println("="*80)
              val sortedSol = solution.toArray.sortWith(_._1.name < _._1.name)
              for((pred,sol) <- sortedSol) {
                val cl = HornClause(RelVar(pred.name,
                  (0 until pred.arity).zip(HornPredAbs.predArgumentSorts(pred).map(
                    lazabs.prover.PrincessWrapper.sort2Type(_))).map(p =>
                    Parameter("_" + p._1,p._2)
                  ).toList),
                  List(Interp(lazabs.prover.PrincessWrapper.formula2Eldarica(sol,
                    Map[ap.terfor.ConstantTerm,String]().empty,false))))
                println(lazabs.viewer.HornSMTPrinter.printFull(cl, true))
              }
              println("="*80 + "\n")
            }

            val contexts = reader.getFunctionContexts
            val loopInvariants = reader.getLoopInvariants
            if ((displayACSL || log) &&
              (contexts.nonEmpty || loopInvariants.nonEmpty)) {

              val solutionProcessors = Seq(
                ADTExploder
                // add additional solution processors here
              )
              var processedSolution: SolutionProcessor.Solution = solution
              // iteratively process the solution using all solution processors
              // this will only process the pre/post predicates' solutions due
              // to the second argument
              for (processor <- solutionProcessors) {
                processedSolution =
                  processor(processedSolution)() // will process all predicates
              }

              println("\nInferred ACSL annotations")
              println("="*80)
              // line numbers in contract vars (e.g. x/1) are due to CCVar.toString
              for ((fun, ctx) <- contexts
                   if maybeEnc.isEmpty ||
                      !maybeEnc.get.prePredsToReplace.contains(ctx.prePred.pred) &&
                      !maybeEnc.get.postPredsToReplace.contains(ctx.postPred.pred)) {
                
                var acslProcessedSolution = processedSolution

                if (modelledHeapRes) {
                  def applyProcessor(processor: ContractProcessor, 
                                    solution: SolutionProcessor.Solution
                                    ): SolutionProcessor.Solution = {
                    printlnDebug(s"----- Applying $processor to $fun.")
                    val (newPrecondition, newPostcondition) =
                      processor(solution, fun, ctx)
                    printlnDebug("----- Precondition:")
                    printlnDebug(solution(ctx.prePred.pred).toString)
                    printlnDebug("----- New Precondition:")
                    printlnDebug(newPrecondition.toString)
                    printlnDebug("----- Postcondition:")
                    printlnDebug(solution(ctx.postPred.pred).toString)
                    printlnDebug("----- New Postcondition:")
                    printlnDebug(newPostcondition.toString)
                    solution + (ctx.prePred.pred -> newPrecondition) +
                      (ctx.postPred.pred -> newPostcondition)
                  }

                  import ap.parser.IFormula
                  import ap.parser.IExpression.Predicate
                  def addClauses(clauses: Option[IFormula],
                                 predicate: Predicate,
                                 solution: SolutionProcessor.Solution)
                  : SolutionProcessor.Solution = {
                    clauses match {
                      case Some(clauseFormula) =>
                        val newContractCondition =
                          solution(predicate).asInstanceOf[IFormula] &
                          clauseFormula
                        solution + (predicate -> newContractCondition)
                      case None =>
                        solution
                    }  
                  }

                  acslProcessedSolution =
                    applyProcessor(PostconditionSimplifier, acslProcessedSolution)

                  val heapPropProcessors = Seq(
                    PointerPropProcessor,
                    AssignmentProcessor
                  )

                  for (prsor <- heapPropProcessors) {
                    val contractInfo = ContractInfo(solution, fun, ctx)
                    val preCCI =
                      ContractConditionInfo(ctx.prePred.pred, contractInfo)
                    val postCCI =
                      ContractConditionInfo(ctx.postPred.pred, contractInfo)

                    printlnDebug(s"----- Applying $prsor to precondition of $fun")
                    printlnDebug("----- Precondition:")
                    printlnDebug(preCCI.contractCondition.toString)

                    val preClauses =
                      prsor.getClauses(preCCI.contractCondition, preCCI)

                    printlnDebug("Result:")
                    printlnDebug(preClauses.toString)

                    acslProcessedSolution = addClauses(
                      preClauses, ctx.prePred.pred, acslProcessedSolution)

                    printlnDebug(s"----- Applying $prsor to postcondition of $fun")
                    printlnDebug("----- Postcondition:")
                    printlnDebug(postCCI.contractCondition.toString)

                    val postClauses =
                      prsor.getClauses(postCCI.contractCondition, postCCI)

                    printlnDebug("----- Result:")
                    printlnDebug(postClauses.toString)

                    acslProcessedSolution = addClauses(
                      postClauses,ctx.prePred.pred, acslProcessedSolution)
                  }

                  val printHeapExprProcessors = Seq(
                    TheoryOfHeapProcessor,
                    ADTSimplifier,
                    ADTExploder,
                    ToVariableForm,
                    ACSLExpressionProcessor,
                    ClauseRemover)

                  for (processor <- printHeapExprProcessors) {
                    acslProcessedSolution = applyProcessor(processor, acslProcessedSolution)
                  }
                }

                printlnDebug("----- Applying ACSLLineariser to precondition:")
                printlnDebug(acslProcessedSolution(ctx.prePred.pred).toString)

                val fPre = ACSLLineariser asString
                             acslProcessedSolution(ctx.prePred.pred)

                printlnDebug("----- Result:")
                printlnDebug(fPre.toString)
                printlnDebug("----- Applying ACSLLineariser to postcondition:")
                printlnDebug(acslProcessedSolution(ctx.postPred.pred).toString)

                val fPost = ACSLLineariser asString acslProcessedSolution(ctx.postPred.pred)
                printlnDebug("----- Result:")
                printlnDebug(fPost)

                // todo: implement replaceArgs as a solution processor
                // replaceArgs does a simple string replacement (see above def)
                val fPreWithArgs =
                  replaceArgs(fPre, ctx.prePredACSLArgNames)
                val fPostWithArgs =
                  replaceArgs(fPost, ctx.postPredACSLArgNames)

                println("/* contracts for " + fun + " */")
                println("/*@")
                print(  "  requires "); println(fPreWithArgs + ";")
                print(  "  ensures "); println(fPostWithArgs + ";")
                println("*/")
              }
              if(loopInvariants nonEmpty) {
                println("/* loop invariants */")
                for ((name, (inv, srcInfo)) <- loopInvariants) {
                  val fInv = ACSLLineariser asString processedSolution.find(p =>
                    p._1.name.stripPrefix("inv_") == inv.pred.name).get._2
                  val fInvWithArgs =
                    replaceArgs(fInv, inv.argVars.map(_.name))
                  println("\n/* loop invariant for the loop at line " +
                          srcInfo.line + " */")
                  println("/*@")
                  print(  "  loop invariant "); println(fInvWithArgs + ";")
                  println("*/")
                }
              }
              println("="*80 + "\n")
            }
          case None =>
        }
        Safe
      case Right(cex) => {
        println("UNSAFE")

      val clauseToUnmergedRichClauses : Map[Clause, Seq[CCClause]] = cex._2.iterator.map {
          case (_, clause) =>
            val richClauses : Seq[CCClause]= mergedToOriginal get clause match {
              case Some(clauses) =>
                for (Some(richClause) <- clauses map reader.getRichClause) yield
                  richClause
              case None =>
                reader.getRichClause(clause) match {
                  case None => Nil
                  case Some(richClause) => Seq(richClause)
                }
            }
            (clause -> richClauses)
        }.toMap

        if (plainCEX) {
          if (cex._1 == Nil) { // todo: print cex when hornConcurrency no longer returns Nil
            println("This counterexample cannot be printed in the " +
                    "console, use -eogCEX for a graphical view.")
          }
          else {
            println
            hornconcurrency.VerificationLoop.prettyPrint(cex)
            if (system.processes.size == 1 &&
                system.processes.head._2 == ParametricEncoder.Singleton) { // todo: print failed assertion for concurrent systems
              val violatedAssertionClause = cex._2.head._2
              clauseToUnmergedRichClauses get violatedAssertionClause match {
                case Some(richClauses) if richClauses != Nil =>
                  assert(richClauses.size == 1)
                  println("Failed assertion:\n" + richClauses.head.toString)
                  println
                case None                                    =>
              }
            }
          }
        }
        if (!pngNo) { // dotCEX and maybe eogCEX
          if(system.processes.size == 1 &&
             system.processes.head._2 == ParametricEncoder.Singleton) {
            Util.show(cex._2, "cex",
                      clauseToUnmergedRichClauses.map(c => (c._1 ->
                                                            c._2.filter(_.srcInfo.nonEmpty).map(_.srcInfo.get))),
                      reader.PredPrintContext.predArgNames,
                      reader.PredPrintContext.predSrcInfo,
                      reader.PredPrintContext.isUninterpretedPredicate)
          } else {
            println("Cannot display -eogCEX for concurrent processes, try -cex.")
          }
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
    case t: java.lang.StackOverflowError =>
      if(devMode)
        t.printStackTrace
      printError(StackOverflow.toString)
      ExecutionSummary(StackOverflow, Nil, modelledHeap,
        programTimer.s, preprocessTimer.s)
    case t: Exception =>
      if(devMode)
        t.printStackTrace
      printError(t.getMessage)
      ExecutionSummary(OtherError(t.getMessage), Nil, modelledHeap,
        programTimer.s, preprocessTimer.s)
    case t: AssertionError =>
      printError(t.getMessage)
      if(devMode)
        t.printStackTrace
      ExecutionSummary(OtherError(t.getMessage), Nil, modelledHeap,
        programTimer.s, preprocessTimer.s )
  }

}
