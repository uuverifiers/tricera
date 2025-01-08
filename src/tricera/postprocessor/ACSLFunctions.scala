/**
 * Copyright (c) 2023 Oskar Soederberg. All rights reserved.
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

/* ACSLExpression.scala
 *  
 * Defines IFunctiions and Predicates corresponding to ACSL expressions. 
 */

package tricera.postprocessor

import ap.parser._
import ap.terfor.ConstantTerm
import IExpression._
import ap.types.MonoSortedIFunction
import tricera.{ResultUtils, IFuncParam}

object ACSLExpression {
  val valid = new Predicate("\\valid", 1)
  val deref = new IFunction("deref", 1, false, false) // *p
  val oldDeref = new IFunction("oldDeref", 1, false, false) // \old(*p)
  val derefOldPointer =
    new IFunction("derefOldPointer", 1, false, false) // *\old(p)
  val arrow = new IFunction("arrow", 2, false, false) // p->a
  val arrowOldPointer =
    new IFunction("arrowOldPointer", 2, false, false) // \old(p)->a
  val oldArrow = new IFunction("oldArrow", 2, false, false) // \old(p)->a
  val separated = new Predicate("\\separated", 2) // \separated(p1, p2)

  val functions = Set(deref, oldDeref, derefOldPointer, arrow, arrowOldPointer, oldArrow)
  val predicates = Set(valid, separated)

  // Here a ConstantTerm is introduced as a container for the variable name
  def derefFunApp(
      derefFunction: IFunction,
      pointer: ISortedVariable,
      quantifierDepth: Int,
      cci: ContractConditionInfo
  ) = {
    val name = cci.stripOld(cci.getVarName(pointer, quantifierDepth).get)
    IFunApp(derefFunction, Seq(IConstant(new ConstantTerm(name))))
  }

  def arrowFunApp(
      arrowFunction: IFunction,
      pointer: ISortedVariable,
      selector: MonoSortedIFunction,
      quantifierDepth: Int,
      cci: ContractConditionInfo
  ) = {
    val pointerName = cci.stripOld(
      cci.getVarName(pointer, quantifierDepth).get
    )
    val selectorName = selector.name
    IFunApp(
      arrowFunction,
      Seq(
        IConstant(new ConstantTerm(pointerName)),
        IConstant(new ConstantTerm(selectorName))
      )
    )
  }

  def separatedPointers(pointers: Set[IFuncParam]): IFormula = {
    def asSeparatedAtom(p1: IFuncParam, p2: IFuncParam): IFormula = {
      IAtom(separated, Seq(p1, p2))
    }

    val ptrs = pointers.map(p => stripOld(p))
    if (ptrs.size >= 2) {
      ptrs
        .toSeq
        .combinations(2)
        .map({ case Seq(p1, p2) => asSeparatedAtom(p1, p2) })
        .reduceLeft(_ & _)
    } else {
      IBoolLit(true)
    }
  }

  def validPointers(pointers: Set[IFuncParam]): IFormula = {
    def validAtom(p: IFuncParam):IFormula = IAtom(valid, Seq(p)) 

    val ptrs = pointers.map(p => stripOld(p))
    ptrs.size match {
      case s if s >= 2 =>
        ptrs
          .map((p) => validAtom(p))
          .reduceLeft(_ & _)
      case s if s == 1 =>
        validAtom(ptrs.head)
      case _ => IBoolLit(true)
    }
  }

  private def stripOld(p: IFuncParam): IFuncParam = {
    val IFuncParam(constTerm) = p
    IFuncParam(new ConstantTerm(ResultUtils.stripOld(constTerm.name)))  
  }
}
