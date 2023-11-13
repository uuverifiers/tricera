/**
 * Copyright (c) 2021-2023 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
import ap.parser.IExpression.ConstantTerm
import ap.parser._
import ap.theories.Theory
import ap.terfor.preds.Predicate
import ap.theories.ExtArray
import ap.types.{MonoSortedIFunction, SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import tricera.concurrency.ccreader.CCExceptions._
import tricera.concurrency.concurrent_c.Absyn._
import tricera.params.TriCeraParameters

import scala.collection.mutable.{ArrayBuffer => MArray, HashMap => MHashMap, Stack => MStack}

object Util {
  def warn(msg : String) : Unit =
    Console.err.println("Warning: " + msg)

  def printlnDebug(msg : String) : Unit = {
    if (params.TriCeraParameters.get.printDebugMessages)
      println(msg)
  }

  case class SourceInfo (line : Int, col : Int, offset : Int)

  private def getIntegerField(obj: Any, fieldName: String): Int = {
    val field =obj.getClass.getDeclaredField(fieldName)
    field.getInt(obj)
  }
  def getSourceInfo(obj : Any) : SourceInfo = {
    try {
      val line = getIntegerField(obj, "line_num")
      val col = getIntegerField(obj, "col_num")
      val offset = getIntegerField(obj, "offset")
      SourceInfo(line, col, offset)
    } catch {
      case _ : Throwable => throw new Exception("Could not extract line number from " +
        obj.getClass)
    }
  }

  // extract the line number of the last statement
  // todo: this might be missing cases
  def getLastSourceInfo (obj : Any) : SourceInfo = {
    obj match {
      case s : LabelS => getLastSourceInfo(s.labeled_stm_)
      case s : CompS => getLastSourceInfo(s.compound_stm_)
      case s : ExprS => getLastSourceInfo(s.expression_stm_)
      case s : SelS => getLastSourceInfo(s.selection_stm_)
      case s : IterS => getLastSourceInfo(s.iter_stm_)
      case s : JumpS => getLastSourceInfo(s.jump_stm_)
      case s : DecS => getLastSourceInfo(s.dec_)
      case s : AtomicS => getLastSourceInfo(s.atomic_stm_)
      case s : ScompTwo => getLastSourceInfo(s.liststm_.getLast)
      case s : SselOne => getLastSourceInfo(s.stm_)
      case s : SselTwo => getLastSourceInfo(s.stm_2)
      case s : SselThree => getLastSourceInfo(s.stm_)
      case s : SiterOne =>  getLastSourceInfo(s.stm_)
      case s : SiterTwo =>  getLastSourceInfo(s.exp_)
      case s : SiterThree =>  getLastSourceInfo(s.stm_)
      case s : SiterFour =>  getLastSourceInfo(s.stm_)
      case s : SatomicTwo =>  getLastSourceInfo(s.stm_)
      case s : SlabelOne => getLastSourceInfo(s.stm_)
      case s : SlabelTwo => getLastSourceInfo(s.stm_)
      case s : SexprTwo => getLastSourceInfo(s.exp_)
      case e : Ecomma => getLastSourceInfo(e.exp_2)
      case e : Eassign => getLastSourceInfo(e.exp_2)
      case e : Econdition => getLastSourceInfo(e.exp_2)
      case e : Elor => getLastSourceInfo(e.exp_2)
      case e : Eland => getLastSourceInfo(e.exp_2)
      case e : Ebitor => getLastSourceInfo(e.exp_2)
      case e : Ebitexor => getLastSourceInfo(e.exp_2)
      case e : Ebitand => getLastSourceInfo(e.exp_2)
      case e : Eeq => getLastSourceInfo(e.exp_2)
      case e : Eneq => getLastSourceInfo(e.exp_2)
      case e : Elthen => getLastSourceInfo(e.exp_2)
      case e : Egrthen => getLastSourceInfo(e.exp_2)
      case e : Ele => getLastSourceInfo(e.exp_2)
      case e : Ege => getLastSourceInfo(e.exp_2)
      case e : Eleft => getLastSourceInfo(e.exp_2)
      case e : Eright => getLastSourceInfo(e.exp_2)
      case e : Eplus => getLastSourceInfo(e.exp_2)
      case e : Eminus => getLastSourceInfo(e.exp_2)
      case e : Etimes => getLastSourceInfo(e.exp_2)
      case e : Ediv => getLastSourceInfo(e.exp_2)
      case e : Emod => getLastSourceInfo(e.exp_2)
      case e : Earray => getLastSourceInfo(e.exp_2)
      case e : Efunkpar => getLastSourceInfo(e.listexp_.getLast)
      case _ => getSourceInfo(obj)
    }
  }

  def getLineString(exp: Exp): String = {
    val sourceInfo = getSourceInfo(exp)
    getLineString(Some(sourceInfo))
  }

  def getLineString(maybeSourceInfo : Option[SourceInfo]) : String = {
    maybeSourceInfo match {
      case Some(sourceInfo) =>
        "At line " + sourceInfo.line + " (offset " + sourceInfo.offset + "): "
      case None => ""
    }
  }

  /**
   * Helper function to write to ADT fields. This code was taken almost verbatim
   * from the similar method in the ap.theories.Heap.
   * todo: move this to another class, maybe a new one for helper functions
   *   for IFormulas (or add to Princess)
   * @param lhs : the ADT field term to be written to. This should be an IFunApp,
   *            where the outermost function is a selector of the ADT, the
   *            innermost function is a heap read to the ADT on the heap, the
   *            innermost+1 function is the getter of the ADT, and any
   *            intermediate functions are other selectors
   *            e.g. select(a(s), i) or  (in C: s.a[i])
   * @param rhs : the new value for the field, e.g. 42
   * this would return a new term, such as: S(store(a, i, 42))
   * @return    : the new ADT term
   */
  def writeADT (lhs : IFunApp, rhs : ITerm,
                adtCtors : Seq[MonoSortedIFunction],
                adtSels : Seq[Seq[MonoSortedIFunction]]) : ITerm = {
    import IExpression.toFunApplier

    case class ADTFieldPath (ctor : MonoSortedIFunction,
                                     sels : Seq[MonoSortedIFunction],
                                     updatedSelInd : Int)
    def generateADTUpdateStack (termPointingToADTField : IFunApp)
    : (List[ADTFieldPath], ITerm) = {
      val ADTUpdateStack = new MStack[ADTFieldPath]

      def fillParentStack (fieldTerm : IFunApp) : ITerm = {
        val maybeArrayTheory = ExtArray.Select.unapply(fieldTerm.fun)
        assert(fieldTerm.args.size == 1 || maybeArrayTheory.nonEmpty)
        fieldTerm.args.head match {
          case nested : IFunApp if adtCtors.exists(c =>
            c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort) &&
            ExtArray.Select.unapply(nested.fun).isEmpty =>

            // here two possibilities:
            // one is that the last level resSort is a getter
            //   (e.g. getS that has the same resSort as a ctor)
            // second is that the last level is simply the ctor
            val ctorInd =
              if(adtCtors contains nested.fun) { // first case
                adtCtors indexOf nested.fun
              } else { // second case
                adtCtors.indexWhere(c =>
                  c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort)
              }

            val sels = adtSels(ctorInd)
            val thisSelInd =
              adtSels(ctorInd).indexWhere(s => s == fieldTerm.fun)
            ADTUpdateStack.push(
              ADTFieldPath(adtCtors(ctorInd), sels, thisSelInd))
            // then move on to nested parents
            fillParentStack(nested)
          case _ => fieldTerm
        }
      }
      val rootTerm = fillParentStack (termPointingToADTField)
      (ADTUpdateStack.toList, rootTerm)
    }


    def updateADT(adtStack : List[ADTFieldPath], parentTerm : ITerm,
                  newVal : ITerm) : ITerm = {
      adtStack match {
        case Nil => // last level
          newVal
        case parent :: tl => import IExpression.toFunApplier
          val newTerm = updateADT(tl, parentTerm, newVal)
          val args = for (i <- parent.sels.indices) yield {
            if (i == parent.updatedSelInd) newTerm
            else parent.sels(i)(parentTerm)
          }
          parent.ctor(args : _*)
      }
    }

    val (adtStack, rootTerm) = generateADTUpdateStack(lhs)
    val newTerm = updateADT(adtStack, rootTerm, rhs)
    rootTerm match {
      case IFunApp(f, args) =>
        f match {
          case ExtArray.Select(arr) => // Object select (select(a, i))
            arr.store(args(0), args(1), newTerm)
          case _ => throw new TranslationException("Could not determine write from " +
            "the lhs: " + lhs)
        }
      case _ => throw new TranslationException("Could not determine write from " +
        "the lhs: " + lhs)
    }
  }

////////////////////////////////////////////////////////////////////////////////
  import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}

  /**
   *  Methods to print lazabs.horn.bottomup.Util.Dag
   *  The raw counterexamples from VerificationLoop are Dags.
  * */

  def show[D](d : Dag[D], name : String,
              clauseSrcInfos : Map[Clause, Seq[SourceInfo]], // todo: this is actually a bit overkill, we do not need the rich clause, only used in assertions (for others we look at predicate lines)
              predArgNames : IExpression.Predicate => Seq[String],
              predSrcInfos : IExpression.Predicate => Option[SourceInfo],
              isUnintPred  : Predicate => Boolean) : Unit = {
    if (!TriCeraParameters.get.pngNo) {
      val runTime = Runtime.getRuntime
      val filename = if (TriCeraParameters.get.dotSpec)
        TriCeraParameters.get.dotFile
      else
        "dag-graph-" + name + ".dot"
      val dotOutput = new java.io.FileOutputStream(filename)
      Console.withOut(dotOutput) {
        dotPrint(d, clauseSrcInfos, predArgNames, predSrcInfos, isUnintPred)
      }
      dotOutput.close

      if (TriCeraParameters.get.eogCEX) {
        var proc = runTime.exec( "dot -Tpng " + filename + " -o " + filename + ".png" )
        proc.waitFor
        val imageViewer = if (System.getProperty("os.name") == "Mac OS X") "open -a Preview" else "eog"
        proc = runTime.exec( imageViewer + " " + filename + ".png")
        //    proc.waitFor
      }
    }
  }

  val colors = Seq( // K Kelly, Color Eng., 3 (6) (1965), colors of max contrast
    //"FFB300", // Vivid Yellow
    "803E75", // Strong Purple
    "FF6800", // Vivid Orange
    //"A6BDD7", // Very Light Blue
    "C10020", // Vivid Red
    "CEA262", // Grayish Yellow
    "817066", // Medium Gray
    "007D34", // Vivid Green
    "F6768E", // Strong Purplish Pink
    "00538A", // Strong Blue
    "FF7A5C", // Strong Yellowish Pink
    "53377A", // Strong Violet
    "FF8E00", // Vivid Orange Yellow
    "B32851", // Strong Purplish Red
    //"F4C800", // Vivid Greenish Yellow
    "7F180D", // Strong Reddish Brown
    "93AA00", // Vivid Yellowish Green
    "593315", // Deep Yellowish Brown
    "F13A13", // Vivid Reddish Orange
    "232C16"  // Dark Olive Green
  )
  var curColor : Int = 0
  def getNextColor : String = {
    if (curColor >= colors.size-1)
      curColor = 0
    val res = colors(curColor)
    curColor += 1
    res
  }

  def dotPrint[D](dag : Dag[D],
                  clauseSrcInfos : Map[Clause, Seq[SourceInfo]],
                  predArgNames : IExpression.Predicate => Seq[String],
                  predSrcInfos : IExpression.Predicate => Option[SourceInfo],
                  isUnintPred  : Predicate => Boolean) : Unit = {

    val argColorMap = new MHashMap[String, String]

      // new Color((int)(Math.random() * 0x1000000))

    def updateColors (argNames : Seq[String]) : Unit =
      for (arg <- argNames if !(argColorMap contains arg)) {
        argColorMap += ((arg, getNextColor))
      }

    def getGraphVizColored(arg : String) : String = {
      if(argColorMap contains arg)
        "<FONT COLOR=\"#" + argColorMap(arg) + "\"" + ">" + arg + "</FONT>"
      else arg
    }

    println("digraph dag {")

    for ((curNode@DagNode(d@(atom@IAtom(_, _), clause@HornClauses.Clause(_,_,_)), children, next), i) <- dag.subdagIterator.zipWithIndex) {
      val srcInfos = clauseSrcInfos(clause)
      val clauseLine =
        (if (srcInfos.nonEmpty) {
          " (" +
            (if(srcInfos.length > 1) "lines " else "line ") +
            srcInfos.map(_.line).distinct.mkString(",") + ")"
        } else {
          ""
        })
      atom.pred match {
        case HornClauses.FALSE =>
          //println("" + i + "[label=\"" + clause.toPrologString + "\"];")
          println("" + i + "[shape=box, color=\"red\", label=\"" + "false" +
            (if (clauseLine != "") "\n" + clauseLine else "") +
            "\"];")
        case _ =>
          // atom.args contains values, clause.head.args contains names
          val curArgs = predArgNames(clause.head.pred) //clause.head.args.map(_ toString)
          val curArgValues = curArgs.zip(atom.args.map(_ toString)).toMap

          val unintPredArgs = new MArray[String]
          val prevArgs = new MArray[String]
          val prevArgValues = new MHashMap[String, String]
          for(child <- children) curNode.subdagIterator.toList(child) match {
            case DagNode((IAtom(pred, args), HornClauses.Clause(headAtom, _, _)), _, _) =>
              prevArgs ++= predArgNames(headAtom.pred)
              prevArgValues ++= prevArgs zip args.map(_ toString)
              if(isUnintPred(pred))
                predArgNames(headAtom.pred).foreach(unintPredArgs +=)
            case _ =>
          }

          updateColors(curArgs ++ prevArgs)

          val expiredArgs =
            if (isUnintPred(atom.pred)) Nil
            else (prevArgs diff curArgs) diff unintPredArgs
          val expiredArgStrings = expiredArgs.map(a => getGraphVizColored(a))
          val newArgs =
            if (isUnintPred(atom.pred)) Nil else curArgs diff prevArgs
          val newArgStrings =
            newArgs.map(arg => getGraphVizColored(arg) + " = " + curArgValues(arg))
          val changedArgs =
            if(isUnintPred(atom.pred)) curArgs
            else (curArgs diff expiredArgs).filter(arg =>
                prevArgValues.contains(arg) &&
                  prevArgValues(arg) != curArgValues(arg))
          val changedArgStrings =
            changedArgs.map(arg => getGraphVizColored(arg) + " = " + curArgValues(arg))

          def getString(s: Seq[String], seqName: String,
                        newLine: Boolean = false): String = {
            if (s.nonEmpty) {
              (if (newLine) "<BR/>" else "") +
                "(" + seqName + ": " + s.mkString(", ") + ")"
            }
            else ""
          }

          println("" + i + "[shape=box, label=<" + atom.pred + clauseLine +
//            (predSrcInfos(atom.pred) match {
//              case Some(srcInfo) => " (near line " + srcInfo.line + ")"
//              case None => ""
//            }) +
            "<BR/>" +
            getString(changedArgStrings, if (isUnintPred(atom.pred)) "args" else "changed args") +
            getString(newArgStrings, "new args",
              newLine = changedArgStrings.nonEmpty) +
            getString(expiredArgStrings, "expired args",
              newLine = changedArgStrings.nonEmpty || newArgStrings.nonEmpty) + ">];")
        //        case _ =>
        //          // should not trigger unless DAG contents are changed from Eldarica
        //          println("" + i + "[label=\"" + d + "\"];")
      }

      case class ConstantTermExt(_name : String)
        extends IExpression.ConstantTerm(_name) {
        override def toString : String =
          getGraphVizColored(name)
      }
      def getColoredConstraint(constr : IFormula) : IFormula = {
        val constants = SymbolCollector.constants(constr)
        val substMap : Map[IExpression.ConstantTerm, ITerm] =
          constants.map(c => (c, IConstant(ConstantTermExt(c.name)))).toMap
        ConstantSubstVisitor(constr, substMap)
      }

      def getConstrString(ind : Int) : String =
        dag(ind) match {
          case (_, clause@HornClauses.Clause(_, body, constraint)) =>
            val constantToBodyArg = new MHashMap[ConstantTerm, IConstant]
            for (atom <- body;
                 (IConstant(arg), i) <- atom.args.zipWithIndex) {
              for (const <- clause.constantsSorted.filter(const => const == arg)) {
                val newConst =
                  const match {
                    case SortedConstantTerm(_, sort) =>
                      new SortedConstantTerm(predArgNames(atom.pred)(i), sort)
                    case _: ConstantTerm =>
                      new ConstantTerm(predArgNames(atom.pred)(i))
                  }
                constantToBodyArg += ((const, IConstant(newConst)))
              }
            }

            val c = ConstantSubstVisitor(constraint.andSimplify(true), constantToBodyArg)

            val conjuncts =
              LineariseVisitor(Transform2NNF(getColoredConstraint(c)), IBinJunctor.And)
            val constrString = (for (conjunct <- conjuncts) yield {
              class GeqAtom(left : ITerm, right : ITerm)
                extends IAtom(new Predicate(" &ge; ", 2), Seq(left, right)) {
                override def toString: String =
                  args(0) + pred.name + args(1)
              }
              class LtAtom(left : ITerm, right : ITerm)
                extends IAtom(new Predicate(" &lt; ", 2), Seq(left, right)) {
                override def toString: String =
                  args(0) + pred.name + args(1)
              }
              object EmptyAtom extends IAtom(new Predicate("", 0), Nil) {
                override def toString: String = ""
              }
              /**
               * Visitor to introduce some operations purely used for pretty-printing
               * purposes.
               */
              object EnrichingVisitor extends CollectingVisitor[Unit, IExpression] {
                override def preVisit(t : IExpression, noArg : Unit) : PreVisitResult = t match {
                  case IExpression.Geq(s, t) =>
                    TryAgain(new GeqAtom(s, t), ())
                  case INot(IExpression.Geq(s, t)) =>
                    TryAgain(new LtAtom(s, t), ())
                  case IExpression.Eq(IConstant(left), IConstant(right))
                    if left.name == right.name =>
                    ShortCutResult(EmptyAtom)
                  case _ =>
                    KeepArg
                }
                def postVisit(t : IExpression,
                              ctxt : Unit, subres : Seq[IExpression]) : IExpression =
                  t update subres
              }

              val enriched = EnrichingVisitor.visit(conjunct, ())

              enriched
            }).filter(c => c != IExpression.i(true) && c.toString.nonEmpty).
              mkString(" /\\ ")
            constrString
          case _ => ""
        }


      //      val additionalStr: String =
      //        (for ((child, bAtom) <- (children zip body).drop(1)) yield {
      //          val argNames = predArgNames(bAtom.pred)
      //          (for((a, b) <- bAtom.args zip argNames
      //               if (dagNode2Context contains dag(ind)) &&
      //                 (dagNode2Context(dag(ind)).newArgsRaw contains a.toString)) yield {
      //            a + "=" + b
      //          }).mkString("<br />")
      //          //              dag(child) match {
      //          //                case (atom, _) =>
      //          //
      //          //                  println(bAtom)
      //          //                case _ =>
      //          //              }
      //        }).mkString("<br />")

      // if we have a non-linear clause, introduce an additional node for incoming
      // edges
      if (children.length > 1) {
        val newInd = dag.size + i
        println("" + newInd + "[shape=point, color=\"black\", label=\"\"];")

        val childExprs = new MArray[IExpression]

        for (c <- children) {
          println("" + (i + c) + "->" + newInd +
            "[ label=<" + getConstrString(i + c) + ">]" + ";") // dir=none to remove arrows
        }

        println("" + newInd + "->" + i +
          "[ label=<" + getConstrString(i) + ">]" + ";")
      } else {
        for (c <- children) {
          println("" + (i + c) + "->" + i +
            "[ label=<" + getConstrString(i) + ">]" + ";")
        }
      }
    }
    println("}")
  }
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
  trait TheoryExtractor {
    def unapply(f : IFunction) : Option[Theory]
  }
  class FunAppsFromExtractorCollector(theoryExtractor : TheoryExtractor)
    extends CollectingVisitor[Int, List[(IFunApp, Theory)]] {
    def postVisit(t: IExpression, boundVars: Int,
                  subres: Seq[List[(IFunApp, Theory)]]): List[(IFunApp, Theory)] = {
      t match {
        case f@IFunApp(fun@theoryExtractor(theory), _) =>
          (f, theory) :: subres.flatten.toList
        case _ => subres.flatten.toList
      }
    }
  }
////////////////////////////////////////////////////////////////////////////////
}
