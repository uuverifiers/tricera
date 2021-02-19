/**
 * Copyright (c) 2015-2021 Philipp Ruemmer,
 *                    2021 Zafer Esen. All rights reserved.
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

import ap.parser.{IBoolLit, IFunApp, ITerm, PrincessLineariser}
import lazabs.horn.bottomup.HornTranslator
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.viewer.HornSMTPrinter
import hornconcurrency.{ParametricEncoder, VerificationLoop}

object ReaderMain {

  var currentId = 0
  val dotFileName =  "DotOutput"
  var mergeNodeId = 0
  var falseNodeId = 0
  val oneNodeForEachFalse = true // separates "FALSE" nodes when outputting dot

  def printClauses(system : ParametricEncoder.System) = {
    println("System transitions:")
    for ((p, r) <- system.processes) {
      r match {
        case ParametricEncoder.Singleton =>
          println("  Singleton thread:")
        case ParametricEncoder.Infinite =>
          println("  Replicated thread:")
      }
      for ((c, sync) <- p) {
        val prefix = "    " + c.toPrologString
        print(prefix + (" " * ((50 - prefix.size) max 2)))
        sync match {
          case ParametricEncoder.Send(chan) =>
            println("chan_send(" + chan + ")")
          case ParametricEncoder.Receive(chan) =>
            println("chan_receive(" + chan + ")")
          case ParametricEncoder.NoSync =>
            println
          case _ =>
        }
      }
    }

    if (!system.timeInvariants.isEmpty) {
      println
      println("Time invariants:")
      for (c <- system.timeInvariants)
        println("  " + c.toPrologString)
    }

    system.backgroundAxioms match {
      case ParametricEncoder.SomeBackgroundAxioms(preds, clauses) => {
        println
        println("Background predicates:")
        println("  " + (preds mkString ", "))
        println
        println("Background axioms:")
        for (c <- clauses)
          println("  " + c.toPrologString)
      }
      case _ =>
        // nothing
    }

    if (!system.assertions.isEmpty) {
      println
      println("Assertions:")
      for (c <- system.assertions)
        println("  " + c.toPrologString)
    }

    if (!system.hints.predicateHints.isEmpty) {
      println
      println("Verification hints:")
      for ((p, preds) <-
             system.hints.predicateHints.toArray.sortBy(_._1.name)) {
        println("  " + p + ": ")
        for (x <- preds) {
//          PrincessLineariser printExpression x
          println("    " + x)
        }
      }
    }

    def show: Unit = {
      import scala.collection.mutable.{HashMap => MHashMap}
      import ap.parser.IAtom
      import PrincessLineariser.asString

      val fname = dotFileName + currentId + ".dot"
      val dotOutput = new java.io.FileWriter(fname)
      dotOutput.write( "digraph lazabs {\n")
      dotOutput.write("{\n\"\" [shape=diamond]\n}\n")

      val falseNodeNames = new MHashMap[String, String]
      val predAtomMapping = new MHashMap[ap.terfor.preds.Predicate, IAtom]
      // creates a mapping from preds to their unmodified atoms, e.g. I(a,b)
      // instead of I(a+1, ...). these appear in the body.
      val systemClauses : List[Clause] =
        (for (p <- system.processes.head._1) yield p._1).toList
      val bgClauses : List[Clause] = (system.backgroundAxioms match {
        case ParametricEncoder.SomeBackgroundAxioms(_, clauses) => clauses
        case _ => Nil
      }).toList

      val allClauses = systemClauses ++ bgClauses ++ system.assertions

      def containsEvalArg (atom : IAtom) : Boolean = {
        atom.args.exists(arg => asString(arg).startsWith("__eval")) ||
        atom.args.exists(arg => arg.isInstanceOf[IFunApp])
      }

      for (c <- allClauses; a <- c.body) {
        predAtomMapping get a.pred match {
          case Some(atom) =>
            if (containsEvalArg(atom) & !containsEvalArg(a))
              predAtomMapping.update(a.pred,a)
          case _ =>
            predAtomMapping += ((a.pred, a))
        }
      }
      for (c <- allClauses) {
        val a = c.head
        predAtomMapping get a.pred match {
          case Some(atom) =>
            if (containsEvalArg(atom) & !containsEvalArg(a))
              predAtomMapping.update(a.pred,a)
          case _ =>
            predAtomMapping += ((a.pred, a))
        }
      }

      def graphUpdate (a : ITerm, b : ITerm) = asString(a) + " := " + asString(b)
      def graphConnect (a : String, b : String) = {
        val actualB = b.toLowerCase match {
          case "false" if oneNodeForEachFalse =>
            (falseNodeNames get a) match {
              case Some(n) => n
              case None =>
                val n = "falseNode" + falseNodeId
                falseNodeId += 1
                falseNodeNames += ((a, n))
                n
            }
          case _ => b
        }
        "\"" + a + "\"" + " -> " + "\"" + actualB + "\""
      }

      def graphLabelConstraint (c : Clause, extraConstraint : String = "") = {
        def reformatConstraints (s : String) = {
          val equalTermPattern = "(&* *(.+) :?= \\2 *&*)".r
          val s2 = equalTermPattern.replaceAllIn(s, "\n")
          val andToNewLinePattern = "(.+ = .+ *)&".r
          val s3 = andToNewLinePattern.replaceAllIn(s2, "$1\n")
          val flattenNewLinesPattern = "\n+".r
          flattenNewLinesPattern.replaceAllIn(s3, "\n")
        }
        val constraint =
          if (c.constraint != IBoolLit(true)) asString(c.constraint) else ""
        reformatConstraints(" [label=" + "\"" + constraint +
          (if (constraint.nonEmpty && extraConstraint.nonEmpty) "\n" else "") +
          reformatConstraints(extraConstraint) + "\"]\n")
      }

      def graphClause (actualHead : IAtom, c : Clause, extraEdgeLabel : String) {
        if (c.body.isEmpty) {
          dotOutput.write(
            graphConnect("", asString(actualHead)) +
              graphLabelConstraint(c, extraEdgeLabel))
        } else if (c.body.size > 1) {
          // create a dot sized merge node for the edges to merge into
          val mergeNode = "dotMergeNode" + mergeNodeId
          dotOutput.write(mergeNode + " [label=\"&\", shape=box];\n")
          mergeNodeId += 1
          for (bodyAtom <- c.body)
            dotOutput.write(
              graphConnect(asString(bodyAtom), mergeNode) + "\n")
          dotOutput.write(
            graphConnect(mergeNode, asString(actualHead)) +
              graphLabelConstraint(c, extraEdgeLabel))
        } else {
          for (bodyAtom <- c.body) {
            dotOutput.write(
              graphConnect(asString(bodyAtom), asString(actualHead)) +
                graphLabelConstraint(c, extraEdgeLabel))
          }
        }
      }

      for (c <- allClauses) {
        predAtomMapping get c.head.pred match {
          case Some(a) =>
            val extraEdgeLabel: String = if (a == c.head) "" // head is unchanged
            else { // head args are updated, move updates to edges
              (for ((arg1, arg2) <- c.head.args zip a.args if arg1 != arg2) yield
                graphUpdate(arg2, arg1)).mkString("\n")
            }
            graphClause(a, c, extraEdgeLabel)
          case None => graphClause(c.head, c, "")
        }
      }

      falseNodeNames.foreach(t =>
        dotOutput.write(t._2 + " [label=\"FALSE\", shape=box, color=red];\n"))

      dotOutput.write( "\n}")

      dotOutput.close

      val runTime = Runtime.getRuntime
      var proc = runTime.exec( "dot -Tpng " + "DotOutput" + currentId + ".dot" + " -o graph" + currentId + ".png" )
      proc.waitFor
      proc = runTime.exec( "eog graph" + currentId + ".png")
      proc.waitFor
      currentId = currentId + 1
    }
    if(tricera.TriCeraParameters.get.prettyPrintDot) show
  }

  def printSMTClauses(system : ParametricEncoder.System) : Unit = {
    val processes = system.processes.unzip._1
    val clauses = processes.flatten.unzip._1
    val timeInvariantClauses = system.timeInvariants
    val assertions = system.assertions
    val bgAxiomClauses = system.backgroundAxioms.clauses

    val translator = new HornTranslator
    println(HornSMTPrinter(translator.horn2Eldarica(clauses ++
      timeInvariantClauses ++ assertions ++ bgAxiomClauses)))
  }

  def main(args: Array[String]) : Unit = {
    ap.util.Debug enableAllAssertions false
    tricera.TriCeraParameters.get.assertions = false

    for (name <- args) {
      val system = 
        CCReader(new java.io.BufferedReader (
                   new java.io.FileReader(new java.io.File (name))),
                 "main")._1

      val smallSystem = system.mergeLocalTransitions
      printClauses(smallSystem)

      println
      new VerificationLoop(smallSystem)
    }
  }

}
