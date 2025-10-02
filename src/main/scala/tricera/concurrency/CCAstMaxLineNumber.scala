/**
 * Copyright (c) 2025 Scania CV AB. All rights reserved.
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

import concurrent_c._
import concurrent_c.Absyn._

/** 
 * Vistor to get the maximum line number of a node and its decendents.
 */
class CCAstMaxLineNumber extends FoldVisitor[Int, Unit] with GetLineNumber {
  override def leaf(x: Unit): Int = 0
  override def combine(x: Int, r: Int, a: Unit): Int = x.max(r)

  override def visit(p: Progr, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Afunc, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Athread, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Global, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Chan, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ignored, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: ExternKeyword, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: StraySemi, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AnnotatedFunc, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NewFuncInt, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NewFunc, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Annot1, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SingleThread, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: ParaThread, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NoDeclarator, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Declarators, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PredDeclarator, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InterpPredDeclarator, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PredicateHint, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PredicateExp, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AChan, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Type, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Storage, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SpecProp, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SpecFunc, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AttrSpec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AsmSpec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Attr, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AttrParam, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: OnlyDecl, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InitDecl, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: HintDecl, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: HintInitDecl, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tvoid, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tbool, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tchar, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tshort, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tint, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tlong, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tfloat, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tdouble, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tsigned, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tunsigned, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tstruct, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tenum, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tclock, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tduration, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: GlobalPrograms, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: LocalProgram, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: LocalBlock, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: LocalReg, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InlineFunSpec1, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InlineFunSpec2, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NoRetFunSpec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Const, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NoOptim, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Restrict1, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Restrict2, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Extension, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Tag, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Unique, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: TagType, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Struct, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Union, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Structen, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: TypeSpec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: QualSpec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Decl, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Field, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: DecField, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: EnumDec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: EnumName, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: EnumVar, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Plain, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: EnumInit, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: BeginPointer, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NoPointer, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Name, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: ParenDecl, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InitArray, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Incomplete, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: MathArray, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NewFuncDec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: OldFuncDec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Point, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PointQual, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PointPoint, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PointQualPoint, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AllSpec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: More, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: OnlyType, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: TypeAndParam, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: TypeHintAndParam, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Abstract, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InitExpr, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InitListOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InitListTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AnInit, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: MoreInit, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PlainType, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: ExtendedType, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PointerStart, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Advanced, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: PointAdvanced, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: WithinParentes, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Array, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: InitiatedArray, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: UnInitiated, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Initiated, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: OldFunction, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NewFunction, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: OldFuncExpr, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: NewFuncExpr, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: LabelS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: CompS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: ExprS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SelS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: IterS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: JumpS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: DecS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AtomicS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AnnotationS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AnnotatedIterS, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SlabelOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SlabelTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SlabelThree, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: ScompOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: ScompTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SexprOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SexprTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SselOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SselTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SselThree, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SiterOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SiterTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SiterThree, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SiterFour, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SjumpOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SjumpTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SjumpThree, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SjumpFour, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SjumpFive, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SatomicOne, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: SatomicTwo, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ecomma, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eassign, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Econdition, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Elor, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eland, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ebitor, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ebitexor, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ebitand, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eeq, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eneq, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Elthen, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Egrthen, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ele, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ege, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eleft, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eright, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eplus, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eminus, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Etimes, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ediv, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Emod, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Etypeconv, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Epreinc, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Epredec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Epreop, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ebytesexpr, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ebytestype, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Earray, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Efunk, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Efunkpar, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eselect, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Epoint, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Epostinc, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Epostdec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Evar, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: EvarWithType, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Econst, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Estring, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Enondet, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Efloat, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Echar, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eunsigned, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Elong, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eunsignlong, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ehexadec, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ehexaunsign, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ehexalong, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ehexaunslong, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eoctal, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eoctalunsign, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eoctallong, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eoctalunslong, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ecdouble, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Ecfloat, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eclongdouble, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Eint, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Especial, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Address, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Indirection, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Plus, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Negative, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Complement, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Logicalneg, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: Assign, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignMul, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignDiv, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignMod, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignAdd, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignSub, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignLeft, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignRight, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignAnd, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignXor, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }

  override def visit(p: AssignOr, arg: Unit): Int = {
    getLineNumber(p).max(super.visit(p, arg))
  }  
}
