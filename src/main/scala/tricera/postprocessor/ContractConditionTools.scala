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

 /* ContractConditionTools.scala
 *  
 * Various tools used for processing contract conditions.
 */

package tricera.postprocessor

import ap.parser._
import IExpression.{Conj, Disj, i}
import ap.theories.Heap
import ap.theories.ADT

trait ExpressionUtils {
  def iterateUntilFixedPoint(
      expr: IExpression,
      apply: IExpression => IExpression
  ): IExpression = {
    val expressions: Stream[IExpression] = Stream.iterate(expr)(apply)
    expressions
      .zip(expressions.tail)
      .collectFirst { case (a, b) if a == b => a }
      .getOrElse(expr)
  }
}

trait IdGenerator {
  def generateId: String = java.util.UUID.randomUUID.toString
}

// Indicates whether an IExpression contains a quantifier
object ContainsQuantifiedVisitor extends CollectingVisitor[Int, Boolean] {
  def apply(expr: IExpression, quantifierDepth: Int): Boolean = {
    ContainsQuantifiedVisitor.visit(expr, quantifierDepth)
  }

  override def preVisit(t: IExpression, quantifierDepth: Int): PreVisitResult =
    t match {
      case v: ISortedQuantified => UniSubArgs(quantifierDepth + 1)
      case ISortedVariable(index, _) =>
        if (index < quantifierDepth)
          ShortCutResult(true)
        else
          ShortCutResult(false)
      case _ => KeepArg
    }

  override def postVisit(
      t: IExpression,
      quantifierDepth: Int,
      subres: Seq[Boolean]
  ): Boolean =
    if (subres.isEmpty) false else subres.reduce(_ || _)
}


// Returns an IExpression where simplifications related to the literals
// true and false have been made
object CleanupVisitor extends CollectingVisitor[Unit, IExpression] {
  def apply(expr: IExpression): IExpression = {
    Rewriter.rewrite(expr, (t) => CleanupVisitor.visit(t, ()))
  }

  override def postVisit(t      : IExpression,
                         arg    : Unit,
                         subres : Seq[IExpression]) : IExpression = t match {
    case Conj(f1, f2) if f1 == i(true)  => f2
    case Conj(f1, f2) if f2 == i(true)  => f1
    case Conj(f1, f2) if f1 == i(false) || f2 == i(false) => i(false)
    case Disj(f1, f2) if f1 == i(true)  || f2 == i(true)  => i(true)
    case Disj(f1, f2) if f1 == i(false) => f2
    case Disj(f1, f2) if f2 == i(false) => f1
    case ISortedQuantified(_, _, IBoolLit(true))  => i(true)
    case ISortedQuantified(_, _, IBoolLit(false)) => i(false)
    case INot(IBoolLit(true))  => i(false)
    case INot(IBoolLit(false)) => i(true)
    case _                     => t
  }
}

// Returns a tuple (newExpression, replacedExpression) where n:th IFormula
// in depth-first left-first order is replaced by newFormula in
// newExpression, and replacedExpression is the expression that was
// substituted
object ReplaceNthIFormulaVisitor {
  def apply(
      expr: IExpression,
      n: Int,
      replaceByFormula: IFormula
  ): (IExpression, Option[IExpression]) = {
    val replaceFormulaVisitor: ReplaceNthIFormulaVisitor =
      new ReplaceNthIFormulaVisitor(n, replaceByFormula)
    val newFormula = replaceFormulaVisitor.visit(expr, ())
    (newFormula, replaceFormulaVisitor.getReplacedFormula)
  }

  class ReplaceNthIFormulaVisitor(n: Int, replaceByFormula: IFormula)
      extends CollectingVisitor[Unit, IExpression] {
    private var formulaCount = 0
    private var formula: Option[IExpression] = None

    override def postVisit(
        t: IExpression,
        arg: Unit,
        subres: Seq[IExpression]
    ): IExpression = t match {
      case f: IFormula if formulaCount == n =>
        formula = Some(f)
        formulaCount += 1
        replaceByFormula
      case f: IFormula =>
        formulaCount += 1
        t.update(subres)
      case _ =>
        t.update(subres)
    }

    def getReplacedFormula: Option[IExpression] = formula
  }
}

// Returns the number of IFormulas in an IExpression
object IFormulaCounterVisitor extends CollectingVisitor[Unit, Int] {
  def apply(expr: IExpression): Int = {
    IFormulaCounterVisitor.visit(expr, ())
  }

  override def postVisit(t: IExpression, arg: Unit, subres: Seq[Int]): Int =
    t match {
      case f: IFormula => subres.sum + 1
      case _           => subres.sum
    }
}

// Match types

object Is_O_Sort {
  def unapply(
      expr: IExpression
  ): Option[IExpression] = expr match {
    case IExpression.EqLit(
          IFunApp(
            ADT.CtorId(_, _),
            Seq(arg)
          ),
          _
        ) =>
      Some(arg)

    case _ => None
  }
}

object TheoryOfHeapFunApp {
  def unapply(
      expr: IExpression
  ): Option[(IFunction, Seq[IExpression])] = expr match {
    case IFunApp(
          function @ Heap.HeapRelatedFunction(heap),
          args
        ) if heap.functions.contains(function) =>
      //  heap.functions.contains(function) excludes functions allocResHeap
      //  and allocResAddr, but those should not be appearing in results
      Some((function, args))

    case _ => None
  }
}

object Var {
  def unapply(
      expr: IExpression
  ): Option[ISortedVariable] = expr match {
    case variable @ ISortedVariable(index, _) =>
      Some(variable)

    case _ => None
  }
}
