package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._
import tricera.Util.printlnDebug

trait CopyAstLocation {
  def copyLocationInformation[T](src: T, dest: T): T = {
    for (field <- Set[String]("col_num", "line_num", "offset")) {
      dest.getClass.getDeclaredField(field).setInt(dest, src.getClass().getDeclaredField(field).getInt(src))
    }
    dest
  }
}

/*
object CCAstCopyWithLocation {
  protected  def copyLocationInformation[T](src: T, dest: T): T = {
    for (field <- Set[String]("col_num", "line_num", "offset")) {
      dest.getClass.getDeclaredField(field).setInt(dest, src.getClass().getDeclaredField(field).getInt(src))
    }
    dest
  }
}
*/

/**
 * Visitor that copies the original nodes, including the source
 * location information.
 */
class CCAstCopyWithLocation[A] extends ComposVisitor[A] with CopyAstLocation {
  override def visit(p: Progr, arg: A): Program = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Afunc, arg: A): External_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Athread, arg: A): External_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Global, arg: A): External_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Chan, arg: A): External_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ignored, arg: A): External_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: ExternKeyword, arg: A): IgnoredDecl = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: StraySemi, arg: A): IgnoredDecl = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AnnotatedFunc, arg: A): Function_def = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NewFuncInt, arg: A): Function_def = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NewFunc, arg: A): Function_def = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Annot1, arg: A): Annotation = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SingleThread, arg: A): Thread_def = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: ParaThread, arg: A): Thread_def = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NoDeclarator, arg: A): Dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Declarators, arg: A): Dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PredDeclarator, arg: A): Dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InterpPredDeclarator, arg: A): Dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PredicateHint, arg: A): Pred_hint = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PredicateExp, arg: A): Pred_interp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AChan, arg: A): Chan_def = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Type, arg: A): Declaration_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Storage, arg: A): Declaration_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SpecProp, arg: A): Declaration_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SpecFunc, arg: A): Declaration_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AttrSpec, arg: A): Extra_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AsmSpec, arg: A): Extra_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Attr, arg: A): Attribute = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AttrParam, arg: A): Attribute = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: OnlyDecl, arg: A): Init_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InitDecl, arg: A): Init_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: HintDecl, arg: A): Init_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: HintInitDecl, arg: A): Init_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tvoid, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tbool, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tchar, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tshort, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tint, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tlong, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tfloat, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tdouble, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tsigned, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tunsigned, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tstruct, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tenum, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tclock, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tduration, arg: A): Type_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: GlobalPrograms, arg: A): Storage_class_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: LocalProgram, arg: A): Storage_class_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: LocalBlock, arg: A): Storage_class_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: LocalReg, arg: A): Storage_class_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InlineFunSpec1, arg: A): Function_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InlineFunSpec2, arg: A): Function_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NoRetFunSpec, arg: A): Function_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Const, arg: A): Type_qualifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NoOptim, arg: A): Type_qualifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Restrict1, arg: A): Type_qualifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Restrict2, arg: A): Type_qualifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Extension, arg: A): Type_qualifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Tag, arg: A): Struct_or_union_spec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Unique, arg: A): Struct_or_union_spec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: TagType, arg: A): Struct_or_union_spec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Struct, arg: A): Struct_or_union = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Union, arg: A): Struct_or_union = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Structen, arg: A): Struct_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: TypeSpec, arg: A): Spec_qual = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: QualSpec, arg: A): Spec_qual = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Decl, arg: A): Struct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Field, arg: A): Struct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: DecField, arg: A): Struct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: EnumDec, arg: A): Enum_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: EnumName, arg: A): Enum_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: EnumVar, arg: A): Enum_specifier = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Plain, arg: A): Enumerator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: EnumInit, arg: A): Enumerator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: BeginPointer, arg: A): Declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NoPointer, arg: A): Declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Name, arg: A): Direct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: ParenDecl, arg: A): Direct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InitArray, arg: A): Direct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Incomplete, arg: A): Direct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: MathArray, arg: A): Direct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NewFuncDec, arg: A): Direct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: OldFuncDec, arg: A): Direct_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Point, arg: A): Pointer = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PointQual, arg: A): Pointer = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PointPoint, arg: A): Pointer = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PointQualPoint, arg: A): Pointer = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AllSpec, arg: A): Parameter_type = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: More, arg: A): Parameter_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: OnlyType, arg: A): Parameter_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: TypeAndParam, arg: A): Parameter_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: TypeHintAndParam, arg: A): Parameter_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Abstract, arg: A): Parameter_declaration = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InitExpr, arg: A): Initializer = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InitListOne, arg: A): Initializer = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InitListTwo, arg: A): Initializer = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AnInit, arg: A): Initializers = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: MoreInit, arg: A): Initializers = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PlainType, arg: A): Type_name = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: ExtendedType, arg: A): Type_name = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PointerStart, arg: A): Abstract_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Advanced, arg: A): Abstract_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: PointAdvanced, arg: A): Abstract_declarator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: WithinParentes, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Array, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: InitiatedArray, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: UnInitiated, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Initiated, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: OldFunction, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NewFunction, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: OldFuncExpr, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: NewFuncExpr, arg: A): Dir_abs_dec = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: LabelS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: CompS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: ExprS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SelS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: IterS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: JumpS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: DecS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AtomicS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AnnotationS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AnnotatedIterS, arg: A): Stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SlabelOne, arg: A): Labeled_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SlabelTwo, arg: A): Labeled_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SlabelThree, arg: A): Labeled_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: ScompOne, arg: A): Compound_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: ScompTwo, arg: A): Compound_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SexprOne, arg: A): Expression_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SexprTwo, arg: A): Expression_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SselOne, arg: A): Selection_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SselTwo, arg: A): Selection_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SselThree, arg: A): Selection_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SiterOne, arg: A): Iter_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SiterTwo, arg: A): Iter_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SiterThree, arg: A): Iter_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SiterFour, arg: A): Iter_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SjumpOne, arg: A): Jump_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SjumpTwo, arg: A): Jump_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SjumpThree, arg: A): Jump_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SjumpFour, arg: A): Jump_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SjumpFive, arg: A): Jump_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SjumpAbort, arg: A): Jump_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SjumpExit, arg: A): Jump_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SatomicOne, arg: A): Atomic_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: SatomicTwo, arg: A): Atomic_stm = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ecomma, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eassign, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Econdition, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Elor, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eland, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ebitor, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ebitexor, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ebitand, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eeq, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eneq, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Elthen, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Egrthen, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ele, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ege, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eleft, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eright, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eplus, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eminus, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Etimes, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ediv, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Emod, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Etypeconv, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Epreinc, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Epredec, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Epreop, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ebytesexpr, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ebytestype, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Earray, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Efunk, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Efunkpar, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eselect, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Epoint, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Epostinc, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Epostdec, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Evar, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: EvarWithType, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Econst, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Estring, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Enondet, arg: A): Exp = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Efloat, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Echar, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eunsigned, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Elong, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eunsignlong, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ehexadec, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ehexaunsign, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ehexalong, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ehexaunslong, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eoctal, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eoctalunsign, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eoctallong, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eoctalunslong, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ecdouble, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Ecfloat, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eclongdouble, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Eint, arg: A): Constant = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Especial, arg: A): Constant_expression = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Address, arg: A): Unary_operator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Indirection, arg: A): Unary_operator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Plus, arg: A): Unary_operator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Negative, arg: A): Unary_operator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Complement, arg: A): Unary_operator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Logicalneg, arg: A): Unary_operator = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: Assign, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignMul, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignDiv, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignMod, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignAdd, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignSub, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignLeft, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignRight, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignAnd, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignXor, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }

  override def visit(p: AssignOr, arg: A): Assignment_op = {
    copyLocationInformation(p, super.visit(p, arg))
  }


  }