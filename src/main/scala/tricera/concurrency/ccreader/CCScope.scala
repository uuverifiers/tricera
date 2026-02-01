/**
 * Copyright (c) 2025 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package tricera.concurrency.ccreader

import ap.parser.IExpression.ConstantTerm
import ap.parser.{ContainsSymbol, IConstant, IExpression, ITerm}
import ap.types.SortedConstantTerm
import ap.util.Seqs.reduceToSize
import lazabs.horn.abstractions.VerificationHints.VerifHintElement
import tricera.params.TriCeraParameters
import tricera.Literals
import tricera.Util.SourceInfo

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet}

class CCScope {
  val variableHints =
    new ArrayBuffer[scala.Seq[VerifHintElement]]

  sealed abstract class CCVars {
    val vars = new ArrayBuffer[CCVar]
    def addVar (v : CCVar) : Int = {
      vars += v
      size - 1
    }
    def size : Int = vars.size
    def lastIndexWhere(name : String, enclosingFunction : String) : Int =
      vars lastIndexWhere(v => v.name == name &&
                               (!v.isStatic || v.enclosingFunctionName.get == enclosingFunction))
    def lastIndexWhere(v : CCVar) : Int = vars lastIndexWhere(_ == v)
    def contains (c : ConstantTerm) : Boolean = vars exists(_.term == c)
    def iterator : Iterator[CCVar] = vars.toSeq.iterator
    def formalVars : scala.Seq[CCVar] = vars.toSeq
    def formalVarTerms : scala.Seq[IConstant] = vars.map(v => IConstant(v.term)).toSeq
    def formalTypes : scala.Seq[CCType] = vars.map(_.typ).toSeq
  }

  object GlobalVars extends CCVars {
    val inits = new ArrayBuffer[CCTerm]
  }
  object LocalVars extends CCVars {
    val frameStack = new mutable.Stack[Int]

    override def addVar (v : CCVar) : Int = {
      variableHints += List()
      super.addVar(v)
    }
    def update(idx : Int, elem : CCVar) {
      vars.update(idx, elem)
    }
    def pop(n : Int) = {
      LocalVars trimEnd n
      variableHints trimEnd n
      assert(variableHints.size == size + GlobalVars.size)
    }

    def lastOption : Option[CCVar] = vars.lastOption
    def last : CCVar = vars.last
    def remove(n : Int): CCVar = {
      assume(n >= 0 && n < size)
      variableHints.remove(n + GlobalVars.size)
      vars.remove(n)
    }
    private def trimEnd(n : Int) = vars dropRightInPlace n
    def pushFrame : frameStack.type = frameStack push size
    def popFrame() : Unit = {
      val newSize = frameStack.pop
      reduceToSize(vars, newSize)
      reduceToSize(variableHints, GlobalVars.size + newSize)
    }
    def getVarsInTopFrame : List[CCVar] =
      (vars takeRight (vars.size - frameStack.last)).toList
  }

  def lookupVarNoException(name : String, enclosingFunction : String)
  : Int = {
    /**
     * @note Usage of `lastIndexWhere` is important for shadowing semantics.
     *       For the same reason, it is important to add static variables,
     *       which are stored as globals, after the globals.
     *       Note that static variables should only be accessible from
     *       enclosing functions where they were declared in.
     */
    LocalVars.lastIndexWhere(name, enclosingFunction) match {
      case -1 => GlobalVars.lastIndexWhere(name, enclosingFunction)
      case i  => i + GlobalVars.size
    }
  }

  def lookupVar(name : String, enclosingFunction : String) : Int = {
    val actualName =
      if (TriCeraParameters.get.showVarLineNumbersInTerms) {
        name.lastIndexOf(CCVar.lineNumberPrefix) match {
          case -1 => name
          case i => name.take(i)
        }
      } else name
    lookupVarNoException(actualName, enclosingFunction)
  }

  def allFormalVars : scala.Seq[CCVar] =
    GlobalVars.formalVars ++ LocalVars.formalVars
  def allFormalVarTerms : scala.Seq[ITerm] =
    GlobalVars.formalVarTerms ++ LocalVars.formalVarTerms
  def allFormalVarTypes : scala.Seq[CCType] =
    GlobalVars.formalTypes ++ LocalVars.formalTypes

  def allFormalCCTerms : scala.Seq[CCTerm] =
    ((for (v <- GlobalVars.iterator)
      yield CCTerm.fromTerm(v.term, v.typ, v.srcInfo)) ++
     (for (v <- LocalVars.iterator)
       yield CCTerm.fromTerm(v.term, v.typ, v.srcInfo))).toList
  def allVarInits : scala.Seq[ITerm] =
    (GlobalVars.inits.toList map (_.toTerm)) ++ LocalVars.formalVarTerms

  def freeFromGlobal(t : IExpression) : Boolean =
    !ContainsSymbol(t, (s:IExpression) => s match {
      case IConstant(c) => GlobalVars contains c // todo: true only with concurrency?
      case _ => false
    })

  def freeFromGlobal(t : CCTerm) : Boolean = t match {
    case CCTerm(s, _, _, None) =>    freeFromGlobal(s)
    case CCTerm(_, _, _, Some(f)) => freeFromGlobal(f)
  }

  def updateVarType(name : String, newType : CCType,
                    enclosingFunction : String) : Unit = {
    val ind = lookupVar(name, enclosingFunction)
    if (ind < GlobalVars.size) {
      val oldVar = GlobalVars.vars(ind)
      GlobalVars.vars(ind) =
        new CCVar(name, oldVar.srcInfo, newType, oldVar.storage)
    } else {
      val oldVar = LocalVars.vars(ind - GlobalVars.size)
      LocalVars.vars(ind - GlobalVars.size) =
        new CCVar(name, oldVar.srcInfo, newType, oldVar.storage)
    }
  }

  // TODO: move this out of here into Symex once refactoring is complete so that we
  //       create only one instance of Symex. Only used in Symex.
  private var tempVarCounter = 0
  private val evalVars = new MHashSet[String]

  def getFreshEvalVar (typ     : CCType,
                       srcInfo : Option[SourceInfo],
                       name    : String = "",
                       storage : VariableStorage = AutoStorage) : CCVar = {
    val varName = {
      if (name.nonEmpty) {
        name
      } else {
        val prelName = "__eval" + (srcInfo match {
          case Some(info) => info.line.toString
          case None => ""
        })
        if (evalVars contains prelName) {
          tempVarCounter += 1
          prelName + "_" + tempVarCounter
        } else {
          evalVars += prelName
          prelName
        }
      }
    }

    val res = new CCVar(varName, srcInfo, typ, storage)
    res
  }

  private var funRetCounter = 0
  def getResVar (typ : CCType) : List[CCVar] = typ match {
    case CCVoid     => Nil
    case t          =>
      funRetCounter += 1
      List(new CCVar(Literals.resultExecSuffix + funRetCounter, None, typ, AutoStorage)) // todo: line no?
  }

}
