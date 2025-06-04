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
 * Vistor to set the line number of AST nodes. The visitor will
 * bump the line number after every node that contains
 * a ";".
 * 
 * This is a bit of an abuse of the FoldVisitor. We are actually
 * not folding anything, we are just updating the line number
 * in place.
 */
class CCAstUpdtLineNum[A](startLineNumber: Int) extends FoldVisitor[Unit, A] with SetLineNumber {
  var lineNumber = startLineNumber
  def bumpLineNumber = {
    if (lineNumber < 0) {
      lineNumber -= 1
    } else {
      lineNumber += 1
    }
  }

  def bumpLineNumberAfter[A](thunk: => A) = {
    val result = thunk
    bumpLineNumber
    result
  }

  override def leaf(x: A): Unit = Unit
  override def combine(x: Unit, r: Unit, a: A): Unit = Unit

  override def visit(p: Progr, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Afunc, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Athread, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Global, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Chan, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ignored, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: ExternKeyword, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: StraySemi, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    bumpLineNumber
    super.visit(p, arg)
  }

  override def visit(p: AnnotatedFunc, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NewFuncInt, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NewFunc, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Annot1, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SingleThread, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: ParaThread, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NoDeclarator, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      val r = super.visit(p, arg)
    }
  }

  override def visit(p: Declarators, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: PredDeclarator, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InterpPredDeclarator, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PredicateHint, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PredicateExp, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AChan, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: Type, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Storage, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SpecProp, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SpecFunc, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AttrSpec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AsmSpec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Attr, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AttrParam, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: OnlyDecl, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InitDecl, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: HintDecl, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: HintInitDecl, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tvoid, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tbool, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tchar, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tshort, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tint, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tlong, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tfloat, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tdouble, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tsigned, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tunsigned, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tstruct, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tenum, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tclock, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tduration, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: GlobalPrograms, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: LocalProgram, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: LocalBlock, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: LocalReg, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InlineFunSpec1, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InlineFunSpec2, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NoRetFunSpec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Const, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NoOptim, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Restrict1, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Restrict2, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Extension, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Tag, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Unique, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: TagType, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Struct, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Union, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Structen, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: TypeSpec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: QualSpec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Decl, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Field, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: DecField, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: EnumDec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: EnumName, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: EnumVar, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Plain, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: EnumInit, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: BeginPointer, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NoPointer, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Name, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: ParenDecl, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InitArray, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Incomplete, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: MathArray, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NewFuncDec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: OldFuncDec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Point, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PointQual, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PointPoint, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PointQualPoint, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AllSpec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: More, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: OnlyType, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: TypeAndParam, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: TypeHintAndParam, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Abstract, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InitExpr, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InitListOne, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InitListTwo, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AnInit, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: MoreInit, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PlainType, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: ExtendedType, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PointerStart, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Advanced, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: PointAdvanced, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: WithinParentes, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Array, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: InitiatedArray, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: UnInitiated, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Initiated, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: OldFunction, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NewFunction, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: OldFuncExpr, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: NewFuncExpr, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: LabelS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: CompS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: ExprS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SelS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: IterS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: JumpS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: DecS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AtomicS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AnnotationS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AnnotatedIterS, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SlabelOne, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SlabelTwo, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SlabelThree, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: ScompOne, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: ScompTwo, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SexprOne, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SexprTwo, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SselOne, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SselTwo, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SselThree, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SiterOne, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SiterTwo, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SiterThree, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SiterFour, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SjumpOne, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SjumpTwo, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SjumpThree, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SjumpFour, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SjumpFive, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SjumpAbort, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SjumpExit, arg: A): Unit = {
    bumpLineNumberAfter {
      setLineNumber(p, lineNumber)
      super.visit(p, arg)
    }
  }

  override def visit(p: SatomicOne, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: SatomicTwo, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ecomma, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eassign, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Econdition, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Elor, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eland, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ebitor, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ebitexor, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ebitand, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eeq, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eneq, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Elthen, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Egrthen, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ele, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ege, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eleft, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eright, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eplus, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eminus, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Etimes, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ediv, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Emod, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Etypeconv, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Epreinc, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Epredec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Epreop, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ebytesexpr, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ebytestype, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Earray, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Efunk, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Efunkpar, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eselect, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Epoint, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Epostinc, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Epostdec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Evar, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: EvarWithType, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Econst, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Estring, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Enondet, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Efloat, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Echar, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eunsigned, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Elong, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eunsignlong, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ehexadec, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ehexaunsign, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ehexalong, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ehexaunslong, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eoctal, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eoctalunsign, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eoctallong, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eoctalunslong, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ecdouble, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Ecfloat, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eclongdouble, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Eint, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Especial, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Address, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Indirection, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Plus, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Negative, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Complement, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Logicalneg, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: Assign, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignMul, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignDiv, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignMod, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignAdd, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignSub, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignLeft, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignRight, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignAnd, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignXor, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }

  override def visit(p: AssignOr, arg: A): Unit = {
    setLineNumber(p, lineNumber)
    super.visit(p, arg)
  }  
}

// object CCAstUpdateLineNumber 
//   extends AbstractVisitor[Int, Int]
//   with SetLineNumber {
//   /* Program */
//   override def visitDefault(p: Program, lineNumber: Int): Int = {
//     setLineNumber(p, lineNumber)
//     p.accept(this, lineNumber)
//   }
  
//   /*  External_declaration */
//   override def visitDefault(p: External_declaration, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  IgnoredDecl */
//   override def visitDefault(p: IgnoredDecl, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Function_def */
//   override def visitDefault(p: Function_def, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Annotation */
//   override def visitDefault(p: Annotation, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Thread_def */
//   override def visitDefault(p: Thread_def, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Dec */
//   override def visitDefault(p: Dec, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Pred_hint */
//   override def visitDefault(p: Pred_hint, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Pred_interp */
//   override def visitDefault(p: Pred_interp, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Chan_def */
//   override def visitDefault(p: Chan_def, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Declaration_specifier */
//   override def visitDefault(p: Declaration_specifier, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Extra_specifier */
//   override def visitDefault(p: Extra_specifier, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Attribute */
//   override def visitDefault(p: Attribute, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Init_declarator */
//   override def visitDefault(p: Init_declarator, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Type_specifier */
//   override def visitDefault(p: Type_specifier, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Storage_class_specifier */
//   override def visitDefault(p: Storage_class_specifier, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Function_specifier */
//   override def visitDefault(p: Function_specifier, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Type_qualifier */
//   override def visitDefault(p: Type_qualifier, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Struct_or_union_spec */
//   override def visitDefault(p: Struct_or_union_spec, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Struct_or_union */
//   override def visitDefault(p: Struct_or_union, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Struct_dec */
//   override def visitDefault(p: Struct_dec, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Spec_qual */
//   override def visitDefault(p: Spec_qual, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Struct_declarator */
//   override def visitDefault(p: Struct_declarator, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Enum_specifier */
//   override def visitDefault(p: Enum_specifier, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Enumerator */
//   override def visitDefault(p: Enumerator, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Declarator */
//   override def visitDefault(p: Declarator, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Direct_declarator */
//   override def visitDefault(p: Direct_declarator, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Pointer */
//   override def visitDefault(p: Pointer, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Parameter_type */
//   override def visitDefault(p: Parameter_type, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Parameter_declaration */
//   override def visitDefault(p: Parameter_declaration, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Initializer */
//   override def visitDefault(p: Initializer, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Initializers */
//   override def visitDefault(p: Initializers, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Type_name */
//   override def visitDefault(p: Type_name, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Abstract_declarator */
//   override def visitDefault(p: Abstract_declarator, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Dir_abs_dec */
//   override def visitDefault(p: Dir_abs_dec, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Stm */
//   override def visitDefault(p: Stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Labeled_stm */
//   override def visitDefault(p: Labeled_stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Compound_stm */
//   override def visitDefault(p: Compound_stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Expression_stm */
//   override def visitDefault(p: Expression_stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Selection_stm */
//   override def visitDefault(p: Selection_stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Iter_stm */
//   override def visitDefault(p: Iter_stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Jump_stm */
//   override def visitDefault(p: Jump_stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Atomic_stm */
//   override def visitDefault(p: Atomic_stm, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Exp */
//   override def visitDefault(p: Exp, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Constant */
//   override def visitDefault(p: Constant, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Constant_expression */
//   override def visitDefault(p: Constant_expression, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Unary_operator */
//   override def visitDefault(p: Unary_operator, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
  
//   /*  Assignment_op */
//   override def visitDefault(p: Assignment_op, lineNumber: Int): Int = {
//     throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
//   }
// }
