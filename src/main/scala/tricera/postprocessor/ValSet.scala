/**
 * Copyright (c) 2023 Oskar Soederberg
 *               2025-2026 Zafer Esen. All rights reserved.
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
import IExpression.{Conj, Disj, Eq, Quantifier}
import ap.theories.ADT
import tricera.{ConstantAsProgVarProxy, ProgVarProxy}

object Val {
  def apply(term1 : ITerm, term2 : ITerm) : Val =
    Val(Set(term1, term2))

  def merge(vals : Set[Val]) : Val =
    vals.reduce((val1, val2) => val1 | val2)
}
case class Val(variants : Set[ITerm]) {
  def +(term : ITerm) : Val =
    Val(variants + term)

  def +(v : Val) : Val =
    Val.merge(Set(this, v))

  def &(v : Val) : Val =
    Val(variants & v.variants)

  def |(v : Val) : Val =
    Val(variants | v.variants)

  def nonEmpty : Boolean =
    variants.nonEmpty

  def equalsTerm(term : ITerm) : Boolean =
    variants.contains(term)

  def equalsOneOf(terms : Set[ITerm]) : Boolean =
    (variants & terms).nonEmpty
}

object ValSet {

  def apply(term1 : ITerm, term2 : ITerm) : ValSet =
    ValSet(Set(Val(term1, term2)))

  def empty : ValSet =
    ValSet(Set.empty[Val])

  def union(valSets : ValSet*): ValSet = {
    valSets.flatMap(_.vals).foldLeft(ValSet.empty) {(acc, v) =>
      val (equalVals, rest) = acc.vals.partition(_ & v nonEmpty)
      val newVal = if (equalVals.nonEmpty) Val.merge(equalVals + v) else v
      ValSet(rest + newVal)
    }
  }

  def intersect(vs1 : ValSet, vs2 : ValSet) : ValSet = {
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

case class ValSet(vals : Set[Val]) {
  def getOrderingKey(term : ITerm) : (Int, String) =
    (termScore(term), term.toString)
  private def termScore(term : ITerm) : Int = term match {
    case IConstant(v : ProgVarProxy) if v.isParameter => 0
    case IConstant(v : ProgVarProxy) if v.isPostExec => 1
    case IConstant(_ : ProgVarProxy) => 2
    case _: IConstant                => 3
    case IFunApp(_, args)            => 10 + args.map(termScore).sum + args.size
    case ITermITE(_, t, e)           => 20 + termScore(t) + termScore(e)
    case _                           => 100
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

  def getVariantVariables(term : ITerm) : Val = getVal(term) match {
    case Some(v) =>
      val variableVariants : Set[ProgVarProxy] = v.variants.collect {
        case ConstantAsProgVarProxy(c) => c
      }
      Val(variableVariants.map(IConstant(_)))
    case None => Val(Set())
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
    Reader.visit(contractCondition, ())

  private object Reader extends CollectingVisitor[Unit, ValSet] {

    override def postVisit(t               : IExpression,
                           arg             : Unit,
                           subres          : Seq[ValSet]) : ValSet = {
      t match {
        case Conj(_, _) =>
          ValSet.union(subres: _*)

        case Disj(_, _) =>
          ValSet.intersect(subres(0), subres(1))

        case Eq(IFunApp(ADT.CtorId(_, _), Seq(_)), _) =>
          ValSet.empty

        case Eq(term1, term2) =>
          ValSet(term1, term2)

        case IIntFormula(IIntRelation.EqZero, term) =>
          ValSet(0, term)

        case IQuantified(Quantifier.EX, _) =>
          // when leaving EX, drop terms containing its v(0), then shift
          // remaining variables down by one, e.g., 
          // EX. v(1) = v(2) --> v(0) = v(1) in the outer context
          // keep equalities derived through the bound variable
          // EX v. x = f(v) & y = f(v) still implies x = y
          ValSet(subres.head.vals.map { value =>
            Val(value.variants.filterNot(t =>
              SymbolCollector.variables(t).exists(_.index == 0))
              .map(t => VariableShiftVisitor(t, 1, -1)))
          }.filter(_.variants.size > 1))

        case _ =>
          // eqs under negation or inside terms are not facts
          ValSet.empty
      }
    }
  }
}
