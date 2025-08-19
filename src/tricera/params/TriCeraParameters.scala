/**
 * Copyright (c) 2015-2025 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package tricera.params

import java.io.FileReader

import lazabs.GlobalParameters
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import tricera.Main.MainException
import tricera.concurrency.CCReader

object TriCeraParameters {
  def get : TriCeraParameters = parameters.value
  val parameters =
    new scala.util.DynamicVariable[TriCeraParameters] (new TriCeraParameters)
}

class TriCeraParameters extends GlobalParameters {
  var arithMode : CCReader.ArithmeticMode.Value =
    CCReader.ArithmeticMode.Mathematical

  var prettyPrintDot : Boolean = false

  var printPP    : Boolean = false
  var dumpPP     : Boolean = false
  var noPP       : Boolean = false
  var logPPLevel : Int = 0 // 0: quiet, 1: errors only, 2: errors + warnings

  var cPreprocessor : Boolean = false

  var dumpSimplifiedClauses : Boolean = false

  var showVarLineNumbersInTerms : Boolean = false

  /**
   * Properties that TriCera should check.
   * Note that reach safety will be checked by default when no other properties
   * are specified. If any other property is specified, reach safety is not
   * checked unless explicitly specified.
   */
  var checkReachSafety : Boolean = false
  var checkMemTrack    : Boolean = false
  var checkValidDeref  : Boolean = false
  var checkValidFree   : Boolean = false
  var checkMemCleanup  : Boolean = false

  /**
   * memtrack is not directly supported by TriCera. Instead, we check for
   * the stronger property memcleanup - safe means safe for memtrack, unsafe
   * means inconclusive.
   * @todo Support memtrack and remove the following field, refactoring the code
   *       that refer to it.
   */
  val useMemCleanupForMemTrack = true

  /**
   * If set, will check all properties in [[memSafetyProperties]].
   * This set should reflect the memsafety category of SV-COMP.
   */
  var checkMemSafety : Boolean = false
  val memSafetyProperties = {
    import tricera.properties._
    Set(MemValidDeref, MemValidTrack, MemValidFree)
  }

  /**
   * If set, will verify each property separately.
   */
  var splitProperties : Boolean = false

  var useArraysForHeap : Boolean = false

  var devMode : Boolean = false
  var printDebugMessages : Boolean = false

  var displayACSL = false
  var inferLoopInvariants = false
  var fullSolutionOnAssert = true

  override def needFullSolution: Boolean =
    (assertions && fullSolutionOnAssert) ||
      displaySolutionProlog || displaySolutionSMT || displayACSL || log ||
      inferLoopInvariants

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

  private val version = "0.4.0"

  private val greeting =
    s"""TriCera v$version.
        |(C) Copyright 2012-2025 Zafer Esen and Philipp Ruemmer
        |Contributors: Pontus Ernstedt, Hossein Hojjat, Oskar Soederberg, Scania CV AB""".stripMargin


  private def parseArgs(args: List[String], shouldExecute : Boolean = true): Boolean =
    args match {
    case Nil => true
    //case "-c" :: rest => drawCFG = true; arguments(rest)
    //case "-r" :: rest => drawRTree = true; arguments(rest)
    case "-f" :: rest => absInFile = true; parseArgs(rest)
    case "-p" :: rest => prettyPrint = true; parseArgs(rest)
    case "-pDot" :: rest => prettyPrint = true; prettyPrintDot = true; parseArgs(rest)
    case "-printPP" :: rest => printPP = true; parseArgs(rest)
    case "-dumpPP" :: rest => dumpPP = true; parseArgs(rest)
    case ppLogOption :: rest if (ppLogOption startsWith "-logPP:") =>
      logPPLevel = (ppLogOption drop 7).toInt; parseArgs(rest)
    case "-noPP" :: rest => noPP = true; parseArgs(rest)
    case "-cpp"  :: rest => cPreprocessor = true; parseArgs(rest)
    case "-dumpClauses" :: rest => printIntermediateClauseSets = true; parseArgs(rest)
    case "-dumpSimplified" :: rest => dumpSimplifiedClauses = true; parseArgs(rest)
    case "-sp" :: rest => smtPrettyPrint = true; parseArgs(rest)
    //      case "-pnts" :: rest => ntsPrint = true; arguments(rest)
    case "-disj" :: rest => disjunctive = true; parseArgs(rest)
    case "-sol" :: rest => displaySolutionProlog = true; parseArgs(rest)
    case "-ssol" :: rest => displaySolutionSMT = true; parseArgs(rest)
    case "-inv" :: rest => inferLoopInvariants = true; parseArgs(rest)
    case "-acsl" :: rest => displayACSL = true; parseArgs(rest)

    case "-mathArrays" :: rest => useArraysForHeap = true; parseArgs(rest)

    case "-abstract" :: rest => templateBasedInterpolation = true; parseArgs(rest)
    case "-abstractPO" :: rest => {
      portfolio = GlobalParameters.Portfolio.Template
      parseArgs(rest)
    }
    case "-portfolio" :: rest => {
      portfolio = GlobalParameters.Portfolio.General
      parseArgs(rest)
    }    case "-abstract:manual" :: rest => {
      templateBasedInterpolation = true
      templateBasedInterpolationType = AbstractionType.Empty
      parseArgs(rest)
    }
    case "-abstract:term" :: rest => {
      templateBasedInterpolation = true
      templateBasedInterpolationType = AbstractionType.Term
      parseArgs(rest)
    }
    case "-abstract:oct" :: rest => {
      templateBasedInterpolation = true
      templateBasedInterpolationType = AbstractionType.Octagon
      parseArgs(rest)
    }
    case "-abstract:relEqs" :: rest => {
      templateBasedInterpolation = true
      templateBasedInterpolationType = AbstractionType.RelationalEqs
      parseArgs(rest)
    }
    case "-abstract:relIneqs" :: rest => {
      templateBasedInterpolation = true
      templateBasedInterpolationType = AbstractionType.RelationalIneqs
      parseArgs(rest)
    }
    case "-abstract:relEqs2" :: rest => {
      templateBasedInterpolation = true
      templateBasedInterpolationType = AbstractionType.RelationalEqs2
      parseArgs(rest)
    }
    case "-abstract:relIneqs2" :: rest => {
      templateBasedInterpolation = true
      templateBasedInterpolationType = AbstractionType.RelationalIneqs2
      parseArgs(rest)
    }
    case "-abstract:off" :: rest => {
      templateBasedInterpolation = false
      parseArgs(rest)
    }
    case tTimeout :: rest if (tTimeout.startsWith("-abstractTO:")) =>
      templateBasedInterpolationTimeout =
        (java.lang.Float.parseFloat(tTimeout.drop(12)) * 1000).toInt;
      parseArgs(rest)

    case tFile :: rest if (tFile.startsWith("-hints:")) => {
      cegarHintsFile = tFile drop 7
      parseArgs(rest)
    }

    case "-pHints" :: rest => templateBasedInterpolationPrint = true;
      parseArgs(rest)

    case splitMode :: rest if (splitMode startsWith "-splitClauses:") => {
      splitClauses = splitMode.drop(14).toInt
      parseArgs(rest)
    }
    case aMode :: rest if (aMode startsWith "-arithMode:") => {
      arithMode = aMode match {
        case "-arithMode:math" => CCReader.ArithmeticMode.Mathematical
        case "-arithMode:ilp32" => CCReader.ArithmeticMode.ILP32
        case "-arithMode:lp64" => CCReader.ArithmeticMode.LP64
        case "-arithMode:llp64" => CCReader.ArithmeticMode.LLP64
        case _ =>
          throw new MainException("Unrecognised mode " + aMode)
      }
      parseArgs(rest)
    }

    case "-n" :: rest => spuriousness = false; parseArgs(rest)
    //      case "-i" :: rest => interpolation = true; arguments(rest)
    case "-lbe" :: rest => lbe = true; parseArgs(rest)

    case arrayQuans :: rest if (arrayQuans.startsWith("-arrayQuans:")) =>
      if (arrayQuans == "-arrayQuans:off")
        arrayQuantification = None
      else
        arrayQuantification = Some(arrayQuans.drop(12).toInt)
      parseArgs(rest)

    case "-noSlicing" :: rest => slicing = false; parseArgs(rest)
    //case "-array" :: rest => arrayRemoval = true; arguments(rest)
    case "-princess" :: rest => princess = true; parseArgs(rest)
    case "-stac" :: rest => staticAccelerate = true; parseArgs(rest)
    case "-dynac" :: rest => dynamicAccelerate = true; parseArgs(rest)
    case "-unap" :: rest => underApproximate = true; parseArgs(rest)
    case "-tem" :: rest => template = true; parseArgs(rest)
    case "-dinq" :: rest => dumpInterpolationQuery = true; parseArgs(rest)
    case "-brew" :: rest => babarew = true; parseArgs(rest)
    /*      case "-bfs" :: rest => searchMethod = BFS; arguments(rest)
          case "-prq" :: rest => searchMethod = PRQ; arguments(rest)
          case "-dfs" :: rest => searchMethod = DFS; arguments(rest)
          case "-rnd" :: rest => searchMethod = RND; arguments(rest)*/
    case tTimeout :: rest if (tTimeout.startsWith("-t:")) =>
      val time = (java.lang.Float.parseFloat(tTimeout.drop(3)) * 1000).toInt
      timeout = Some(time);
      parseArgs(rest)
    case mFuncName :: rest if (mFuncName.startsWith("-m:")) => funcName = mFuncName drop 3; parseArgs(rest)
    case sSolFileName :: rest if (sSolFileName.startsWith("-s:")) => solFileName = sSolFileName.drop(3); parseArgs(rest)
    case "-log" :: rest => setLogLevel(2); parseArgs(rest)
    case "-statistics" :: rest => setLogLevel(1); parseArgs(rest)
    case logOption :: rest if (logOption startsWith "-log:") =>
      setLogLevel((logOption drop 5).toInt); parseArgs(rest)
    case logPredsOption :: rest if (logPredsOption startsWith "-logPreds:") =>
      logPredicates = logPredsOption.drop("-logPreds:".length)
                                    .split(",").toSet
      parseArgs(rest)
    case "-logSimplified" :: rest => printHornSimplified = true; parseArgs(rest)
    case "-logSimplifiedSMT" :: rest => printHornSimplifiedSMT = true; parseArgs(rest)
    case "-dot" :: str :: rest => dotSpec = true; dotFile = str; parseArgs(rest)
    case "-pngNo" :: rest => pngNo = true; parseArgs(rest)
    case "-dotCEX" :: rest => pngNo = false; parseArgs(rest)
    case "-eogCEX" :: rest => pngNo = false; eogCEX = true; parseArgs(rest)
    case "-cex" :: rest => plainCEX = true; parseArgs(rest)
    case "-assert" :: rest => TriCeraParameters.get.assertions = true; parseArgs(rest)
    case "-assertNoVerify" :: rest => TriCeraParameters.get.assertions = true;  TriCeraParameters.get.fullSolutionOnAssert = false; parseArgs(rest)
    case "-dev" :: rest => devMode = true; showVarLineNumbersInTerms = true; parseArgs(rest)
    case "-debug" :: rest => printDebugMessages = true; parseArgs(rest)
    case "-varLines" :: rest => showVarLineNumbersInTerms = true; parseArgs(rest)
    case "-sym" :: rest      =>
      symexEngine = GlobalParameters.SymexEngine.BreadthFirstForward
      parseArgs(rest)
    case symexOpt :: rest if (symexOpt.startsWith("-sym:")) =>
      symexEngine = symexOpt.drop("-sym:".length) match {
        case "dfs" => GlobalParameters.SymexEngine.DepthFirstForward
        case "bfs" => GlobalParameters.SymexEngine.BreadthFirstForward
        case _     =>
          println("Unknown argument for -sym:, defaulting to bfs.")
          GlobalParameters.SymexEngine.BreadthFirstForward
      }
      parseArgs(rest)
    case symexDepthOpt :: rest if (symexDepthOpt.startsWith("-symDepth:")) =>
      symexMaxDepth = Some(symexDepthOpt.drop("-symDepth:".length).toInt)
      parseArgs(rest)

    case "-reachsafety"      :: rest => checkReachSafety = true; parseArgs(rest)
    case "-memsafety"        :: rest => checkMemSafety = true; parseArgs(rest)
    case "-valid-memtrack"   :: rest => checkMemTrack = true; parseArgs(rest)
    case "-valid-deref"      :: rest => checkValidDeref = true; parseArgs(rest)
    case "-valid-free"       :: rest => checkValidFree = true; parseArgs(rest)
    case "-valid-memcleanup" :: rest => checkMemCleanup = true; parseArgs(rest)
    case "-splitProperties"  :: rest => splitProperties = true; parseArgs(rest)

    case arg :: rest if Set("-v", "--version").contains(arg) =>
      println(version); false
    case arg :: rest if Set("-h", "--help").contains(arg) =>
      println(greeting + "\n\nUsage: tri [options] file\n\n" +
  """General options:
    |-h, --help         Show this information
    |-v, --version      Print version number
    |-arithMode:t       Integer semantics: math (default), ilp32, lp64, llp64
    |-mathArrays:t      Use mathematical arrays for modeling program arrays (ignores memsafety properties)
    |-t:time            Set timeout (in seconds)
    |-cex               Show textual counterexamples
    |-dotCEX            Output counterexample in dot format
    |-eogCEX            Display counterexample using eog on Linux and Preview on macOS
    |-sol               Show solution in Prolog format
    |-ssol              Show solution in SMT-LIB format
    |-inv               Try to infer loop invariants
    |-acsl              Print inferred ACSL annotations
    |-log:n             Display progress based on verbosity level n (0 <= n <= 3)
    |                     1: Statistics only
    |                     2: Include invariants
    |                     3: Include counterexamples
    |                     (When using -sym, n > 1 displays derived clauses.)
    |-statistics        Equivalent to -log:1; displays statistics only
    |-log               Equivalent to -log:2; displays progress and invariants
    |-logPreds:<preds>  Log only predicates containing the specified substrings,
    |                     separated by commas. E.g., -logPreds=p1,p2 logs any
    |                     predicate with 'p1' or 'p2' in its name
    |-m:func            Use function func as entry point (default: main)
    |-cpp               Execute the C preprocessor (cpp) on the input file first, this will produce filename.i

    |Checked properties:
    |-reachsafety       Enables checking of explicitly specified properties via assert statements.
    |                   (Enabled by default unless other properties are specified.)
    |-memsafety         Enables checking of all memory safety properties, reflecting the
    |                   memsafety category of SV-COMP. Includes valid-deref, valid-memtrack,
    |                   and valid-free checks.
    |-valid-memtrack    Checks that all allocated memory is tracked.
    |-valid-deref       Checks the validity of pointer dereferences and array accesses.
    |-valid-free        Checks that all occurrences of 'free' are valid.
    |-valid-memcleanup  Checks that all allocated memory is deallocated before program termination.
    |-splitProperties   Check each property separately.

    |Horn clauses:
    |-p                 Pretty-print Horn clauses
    |-pDot              Pretty-print Horn clauses, output in dot format and display it
    |-sp                Pretty-print the Horn clauses in SMT-LIB format
    |-dumpClauses       Write the Horn clauses in SMT-LIB format to input filename.smt2
    |-dumpSimplified    Write simplified Horn clauses in SMT-LIB format to input filename.smt2
    |                   The printed clauses are the ones after Eldarica's default preprocessor
    |-varLines          Print program variables in clauses together with their line numbers (e.g., x:42)

    |Horn engine options (Eldarica):
    |-sym               (Experimental) Use symbolic execution with the default engine (bfs)
    |-sym:x             Use symbolic execution where x : {dfs, bfs}
    |                     dfs: depth-first forward (does not support non-linear clauses)
    |                     bfs: breadth-first forward
    |-symDepth:n        Set a max depth for symbolic execution (underapproximate)
    |                     (currently only supported with bfs)
    |-disj              Use disjunctive interpolation
    |-stac              Static acceleration of loops
    |-lbe               Disable preprocessor (e.g., clause inlining)
    |-arrayQuans:n      Introduce n quantifiers for each array argument (default: 1)
    |-noSlicing         Disable slicing of clauses
    |-hints:f           Read initial predicates and abstraction templates from a file

    |-abstract:t        Interp. abstraction: off, manual, term, oct,
    |                     relEqs, relIneqs, relEqs2 (default), relIneqs2
    |-abstractTO:t      Timeout (s) for abstraction search (default: 2.0)
    |-abstractPO        Run with and w/o interpolation abstraction in parallel
    |-splitClauses:n    Aggressiveness when splitting disjunctions in clauses
    |                     (0 <= n <= 2, default: 1)
    |-pHints            Print initial predicates and abstraction templates
    |-logSimplified     Show clauses after Eldarica preprocessing in Prolog format
    |-logSimplifiedSMT  Show clauses after Eldarica preprocessing in SMT-LIB format

    |TriCera preprocessor:
    |-printPP           Print the output of the TriCera preprocessor to stdout
    |-dumpPP            Dump the output of the TriCera preprocessor to file (input file name + .tri)
    |-logPP:n           Display TriCera preprocessor warnings and errors with verbosity n.
    |                     (0 <= n <= 2, default: 0)
    |-noPP              Turn off the TriCera preprocessor (typedefs are not allowed in this mode)

    |Debugging:
    |-assert            Enable assertions in TriCera
    |-assertNoVerify    Enable assertions, but do not verify solutions
    |""".stripMargin)
      false
    case arg :: _ if arg.startsWith("-") =>
      showHelp
      throw new MainException(s"unrecognized option '$arg'")
    case fn :: rest =>
      fileName = fn; in = new FileReader(fileName); parseArgs(rest)
  }

  var doNotExecute : Boolean = false
  def showHelp : Unit =
    parseArgs(List("-h"))

  def apply(args: List[String]): Unit = {
    if (args isEmpty) {
      doNotExecute = true
      showHelp
    } else if (!parseArgs(reconstructSpaceSeparatedArgs(args))) {
      doNotExecute = true
    }
  }

  private def reconstructSpaceSeparatedArgs(args: List[String]): List[String] = {
    args.foldLeft((List[String](), Option.empty[String])) {
      case ((acc, Some(buffer)), arg) => (acc :+ (buffer + " " + arg), None)
      case ((acc, None), arg) =>
        if (arg.endsWith("\\")) {
          (acc, Some(arg.dropRight(1)))
        } else {
          (acc :+ arg, None)
        }
    }._1
  }
}
