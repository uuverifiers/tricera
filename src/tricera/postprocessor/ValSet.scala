/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025 Zafer Esen. All rights reserved.
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

/* ValSet.scala
 *  
 * Defines objects and classes for treating equivalences. A Val represents a 
 * Set[ITerm] where the ITerms are equivalent. A ValSet is a Set[Vals], allowing to 
 * add new equivalences. ValSet keeps the number of Vals as low as possible, merging 
 * any two Vals whenever they turn out to be equal.
 */
package tricera.postprocessor

import ap.parser._
import IExpression.{Conj, Disj, Eq}
import ap.theories.ADT
import tricera.{ConstantAsProgVarProxy, ProgVarProxy}

object Val {
  def apply(term1: ITerm, term2: ITerm): Val = {
    Val(Set(term1, term2))
  }

  def merge(vals: Set[Val]): Val = {
    vals.reduce((val1, val2) => (val1 | val2))
  }
}
case class Val(variants: Set[ITerm]) {
  def getExplicitForm: Option[ITerm] = variants find { q => { q match {
    case a: Address         => false
    case ConstantAsProgVarProxy(_) => false
    case _                  => true
  }}}

  def getAddrForm: Option[ITerm] = variants find {
    case a: Address => true
    case _          => false
  }

  def getVariableForm: Option[ITerm] = variants find {
    case ConstantAsProgVarProxy(_) => true
    case _             => false
  }

  def +(term: ITerm): Val = {
    Val(variants + term)
  }

  def +(v: Val): Val = {
    Val.merge(Set(this, v))
  }

  def &(v: Val): Val = {
    Val(variants & v.variants)
  }

  def |(v: Val): Val = {
    Val(variants | v.variants)
  }

  def nonEmpty: Boolean = {
    variants.nonEmpty
  }

  def equalsTerm(term: ITerm): Boolean = {
    variants.contains(term)
  }

  def equalsOneOf(terms: Set[ITerm]): Boolean = {
    (variants & terms).nonEmpty
  }
}

object ValSet {

  def apply(term1: ITerm, term2: ITerm): ValSet = {
    ValSet(Set(Val(term1, term2)))
  }

  def empty : ValSet = {
    ValSet(Set.empty[Val])
  }

  def union(valSets : ValSet*): ValSet = {
    valSets.flatMap(_.vals).foldLeft(ValSet.empty) {(acc, v) =>
      val (equalVals, rest) = acc.vals.partition(_ & v nonEmpty)
      val newVal = if (equalVals.nonEmpty) Val.merge(equalVals + v) else v
      ValSet(rest + newVal)
    }
  }

  def intersect(vs1: ValSet, vs2: ValSet): ValSet = {
    if (vs1.isEmpty || vs2.isEmpty) return ValSet.empty

    val allTerms = vs1.vals.flatMap(_.variants) ++ vs2.vals.flatMap(_.variants)
    var resultVs = ValSet.empty

    for (term <- allTerms) {
      val class1 = vs1.getVal(term).map(_.variants).getOrElse(Set(term))
      val class2 = vs2.getVal(term).map(_.variants).getOrElse(Set(term))
      val commonClass = class1.intersect(class2)

      if (commonClass.size > 1) {
        val newV = Val(commonClass)
        resultVs = union(resultVs, ValSet(Set(newV)))
      }
    }
    resultVs
  }
}

case class ValSet(vals: Set[Val]) {
  def getOrderingKey(term : ITerm) : (Int, String) =
    (termScore(term), term.toString)
  private def termScore(term : ITerm) : Int = term match {
    case IConstant(v : ProgVarProxy) if v.isParameter => 0
    case IConstant(v : ProgVarProxy) if v.isPostExec => 1
    case IConstant(_ : ProgVarProxy) => 2
    case _: IConstant               => 3
    case IFunApp(_, args)           => 10 + args.map(termScore).sum + args.size
    case ITermITE(_, t, e)          => 20 + termScore(t) + termScore(e)
    case _                          => 100
  }

  def toCanonicalFormMap : Map[IExpression, ITerm] = {
    vals.flatMap { value =>
      if (value.variants.isEmpty) {
        None
      } else {
        val canonicalRep = value.variants.minBy(getOrderingKey)
        Some(value.variants
                  .filterNot(_ == canonicalRep)
                  .map(_ -> canonicalRep))
      }
    }.flatten.toMap
  }

  def addEquality(term1: ITerm, term2: ITerm): ValSet = {
    val maybeVal1 = getVal(term1)
    val maybeVal2 = getVal(term2)
    (maybeVal1, maybeVal2) match {
      case (Some(val1), Some(val2)) =>
        ValSet(vals.-(val1).-(val2).+(val1 + val2))
      case (Some(v), None) =>
        ValSet(vals.-(v).+(v.+(term2)))
      case (None, Some(v)) =>
        ValSet(vals.-(v).+(v.+(term1)))
      case (None, None) =>
        ValSet(vals.+(Val(term1, term2)))
    }
  }

  def isEmpty : Boolean = vals.isEmpty

  def areEqual(term1: ITerm, term2: ITerm): Boolean = {
    getVal(term1) match {
      case Some(v) => v.equalsTerm(term2)
      case None    => term1 == term2
    }
  }

  def getVal(term: ITerm): Option[Val] = {
    vals.find {
      case v: Val if v.variants.contains(term) => true
      case _                                   => false
    }
  }

  def getExplicitForm(term: ITerm): Option[ITerm] = {
    getVal(term) match {
      case Some(v) => v.getExplicitForm
      case None    => None
    }
  }

  def getVariableForm(term: ITerm): Option[ITerm] = {
    getVal(term) match {
      case Some(v) => v.getVariableForm
      case None    => None
    }
  }

  override def toString = {
    val setsStrings = vals.map { v =>
      v.variants.mkString("{", " :: ", "}")
    }
    setsStrings.mkString("", ", \n", "")
  }
}

object ValSetReader {
  def apply(contractCondition : IExpression) : ValSet =
    Reader.visit(contractCondition, 0)

  private object Reader extends CollectingVisitor[Int, ValSet]
    with ExpressionUtils {

    override def preVisit(t               : IExpression,
                          quantifierDepth : Int) : PreVisitResult = t match {
      case _ : IVariableBinder => UniSubArgs(quantifierDepth + 1)
      case _                   => KeepArg
    }

    override def postVisit(t               : IExpression,
                           quantifierDepth : Int,
                           subres          : Seq[ValSet]) : ValSet = {
      // Replace all v(index) within term where index >= depth with
      // v(index - depth).
      def shiftTerm(term : ITerm) : ITerm =
        VariableShiftVisitor(term,
                             offset = quantifierDepth,
                             shift  = -quantifierDepth)

      t match {
        case Conj(_, _) =>
          ValSet.union(subres: _*)

        case Disj(_, _) =>
          ValSet.intersect(subres(0), subres(1))

        case Eq(IFunApp(ADT.CtorId(_, _), Seq(_)), _) =>
          ValSet.union(subres: _*)

        // ContainsQuantifiedVisitor(term, depth) returns true if
        // term contains an v(n) with n < current quantifierDepth,
        // which implies that term must have an inner quantifier.
        // The case will still trigger if n >= quantifierDepth, which can happen
        // if the terms have IVariables that are not bound to local quantifiers,
        // but are predicate arguments (such as in pre/post condition). In that
        // case we need to subtract the current quantifierDepth from those vars
        // to get their actual terms in the outermost context.
        // e.g., pre(v(0), v(1)) :- (EX. v(1) = v(2)) ...
        // Inside the quantified formula depth = 1, and we add the fact that
        // v(0) = v(1) by shifting the terms by -1.
        case Eq(term1, term2)
          if !ContainsQuantifiedVisitor(term1, quantifierDepth) && // no quantifiers in term1
             !ContainsQuantifiedVisitor(term2, quantifierDepth) => // no quantifiers in term2
          val newEquality = ValSet(shiftTerm(term1), shiftTerm(term2))
          ValSet.union(subres :+ newEquality: _*)

        case IIntFormula(IIntRelation.EqZero, term)
          if !ContainsQuantifiedVisitor(term, quantifierDepth) =>
          val newEquality = ValSet(0, shiftTerm(term))
          ValSet.union(subres :+ newEquality: _*)

        case _ =>
          if (subres.isEmpty) ValSet.empty else ValSet.union(subres: _*)
      }
    }
  }
}
