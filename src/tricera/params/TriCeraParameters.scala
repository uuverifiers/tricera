package tricera.params

import java.io.FileInputStream

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

  var showVarLineNumbersInTerms : Boolean = false

  var shouldTrackMemory : Boolean = false

  var showFailedAssertions : Boolean = false
  var devMode : Boolean = false

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

  private val greeting =
    "TriCera v0.2.\n(C) Copyright 2012-2021 Zafer Esen, Hossein Hojjat, and Philipp Ruemmer"

  private def parseArgs(args: List[String]): Boolean = args match {
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
    case "-dumpClauses" :: rest => printIntermediateClauseSets = true; parseArgs(rest)
    case "-sp" :: rest => smtPrettyPrint = true; parseArgs(rest)
    //      case "-pnts" :: rest => ntsPrint = true; arguments(rest)
    case "-horn" :: rest => horn = true; parseArgs(rest)
    case "-glb" :: rest => global = true; parseArgs(rest)
    case "-disj" :: rest => disjunctive = true; parseArgs(rest)
    case "-sol" :: rest => displaySolutionProlog = true; parseArgs(rest)
    case "-ssol" :: rest => displaySolutionSMT = true; parseArgs(rest)

    case "-memtrack" :: rest => shouldTrackMemory = true; parseArgs(rest)

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
    case "-logSimplified" :: rest => printHornSimplified = true; parseArgs(rest)
    case "-dot" :: str :: rest => dotSpec = true; dotFile = str; parseArgs(rest)
    case "-pngNo" :: rest => pngNo = true; parseArgs(rest)
    case "-dotCEX" :: rest => pngNo = false; parseArgs(rest)
    case "-eogCEX" :: rest => pngNo = false; eogCEX = true; parseArgs(rest)
    case "-cex" :: rest => plainCEX = true; parseArgs(rest)
    case "-assert" :: rest => TriCeraParameters.get.assertions = true; parseArgs(rest)
    case "-cexAsserts" :: rest => showFailedAssertions = true; parseArgs(rest)
    case "-dev" :: rest => devMode = true; showVarLineNumbersInTerms = true; parseArgs(rest)
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
      " -cexAsserts\tDisplay related assertions for counterexamples\n" +
      " -m:func\tUse function func as entry point (default: main)\n" +
      "\n" +
      "Horn engine:\n" +
      " -horn\t\tEnable this engine\n" +
      " -p\t\tPretty Print Horn clauses\n" +
      " -pDot\t\tPretty Print Horn clauses, output in dot format and display it\n" +
      " -printPP\t\tPrint the output of C preprocessor to stdout\n" +
      " -dumpPP\t\tDump the output of C preprocessor to file (input file name + .tri) \n" +
      " -logPP:n\t\tDisplay preprocessor warnings and errors with verbosity n (currently 0 <= n <= 2)\n" +
      " -noPP\t\tTurn off C preprocessor (typedefs are not allowed in this mode) \n" +
      " -sp\t\tPretty print the Horn clauses in SMT-LIB format\n" +
      " -sol\t\tShow solution in Prolog format\n" +
      " -ssol\t\tShow solution in SMT-LIB format\n" +
      " -memtrack\t\tCheck that there are no memory leaks in the input program \n" +
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
      " -splitClauses:n\tAggressiveness when splitting disjunctions in clauses\n" +
      "                \t                     (0 <= n <= 2, default: 1)\n" +

      "\n" +
      "C/C++/TA front-end:\n" +
      " -arithMode:t\tInteger semantics: math (default), ilp32, lp64, llp64\n" +
      " -pIntermediate\tDump Horn clauses encoding concurrent programs\n"
    )
      false
    case fn :: rest =>
      fileName = fn; in = new FileInputStream(fileName); parseArgs(rest)
  }

  var showedHelp : Boolean = false
  def showHelp : Unit = {
    showedHelp = true
    parseArgs(List("-h"))
  }

  def apply(args: List[String]): Unit = {
    if (!parseArgs(args)) showHelp
  }
}
