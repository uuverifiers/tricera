package tricera.postprocessor

import ap.parser._
import scala.collection.immutable.Stack

object PointerPropProcessor extends ContractProcessor {
  def processContractCondition(cci: ContractConditionInfo) = {
    val invForm = ToInvariantFormVisitor(cci.contractCondition)
    val valueSet = ValSetReader.invariant(invForm)
    val explForm = ToExplicitForm.invariant(invForm, valueSet, cci)
    val redForm = HeapReducer(explForm, cci)
    HeapExtractor(redForm, cci) match {
      case Some(heap) =>
        val redValueSet = ValSetReader.invariant(redForm)
        val separatedValid = readSafeVariables(heap, redValueSet)
        cci.contractCondition
          .asInstanceOf[IFormula]
          .&(ACSLExpression.separatedPointers(separatedValid, 0, cci))
          .&(ACSLExpression.validPointers(separatedValid, 0, cci))
      case None => 
        cci.contractCondition
    }
  }

  def readSafeVariables(
      heap: HeapState,
      valueSetWithAddresses: ValSet
  ): Set[ISortedVariable] = {
    heap.storage.keys
      .flatMap(valueSetWithAddresses.getVariableForm(_))
      .asInstanceOf[Set[ISortedVariable]]
  }
}

object HeapExtractor {
  def apply(
      expr: IExpression,
      cci: ContractConditionInfo
  ): Option[HeapState] = {
    (new InvariantHeapExtractor(cci)).visit(expr, ())
  }
}

class InvariantHeapExtractor(cci: ContractConditionInfo)
    extends CollectingVisitor[Unit, Option[HeapState]] {
  override def preVisit(t: IExpression, arg: Unit): PreVisitResult = t match {
    case IEquation(h: ISortedVariable, heap: HeapState) if cci.isHeap(h, 0) =>
      ShortCutResult(Some(heap))
    case _ =>
      KeepArg
  }

  override def postVisit(
      t: IExpression,
      arg: Unit,
      subres: Seq[Option[HeapState]]
  ): Option[HeapState] = t match {
    case h: HeapState => Some(h)
    case _            => subres.collectFirst { case Some(h) => h }
  }
}

object HeapReducer {
  def apply(
      invariantExpression: IExpression,
      cci: ContractConditionInfo
  ): IExpression = {
    (new HeapReducer(cci)).visit(invariantExpression, Stack[String]())
  }
}

class HeapReducer(cci: ContractConditionInfo)
    extends CollectingVisitor[Stack[String], IExpression] {

  override def postVisit(
      t: IExpression,
      quantifierIds: Stack[String],
      subres: Seq[IExpression]
  ): IExpression = {
    t update subres match {
      case QuantifiedVarWithId(ISortedVariable(_, sort), id)
          if sort.name == "Heap" =>
        HeapState.heapById(id)
      case TheoryOfHeapFunApp(
            writeFun,
            Seq(heap: HeapState, addr: Address, obj)
          ) if cci.isWriteFun(writeFun) =>
        heap.write(addr, obj.asInstanceOf[ITerm])
      case TheoryOfHeapFunApp(
            readFun,
            Seq(heap: HeapState, addr: Address)
          ) if cci.isReadFun(readFun) =>
        heap.read(addr)
      case TheoryOfHeapFunApp(
            allocFun,
            Seq(heap: HeapState, obj)
          ) if cci.isAllocFun(allocFun) =>
        heap.alloc(obj.asInstanceOf[ITerm])
      case TheoryOfHeapFunApp(newHeapFun, Seq(allocRes: AllocRes))
          if cci.isNewHeapFun(newHeapFun) =>
        allocRes.newHeap
      case TheoryOfHeapFunApp(newAddrFun, Seq(allocRes: AllocRes))
          if cci.isNewAddrFun(newAddrFun) =>
        allocRes.newAddr
      case _ => t update subres
    }
  }
}

case class QuantifiedVarWithId(variable: ISortedVariable, id: String)
    extends ITerm {
  override def toString = {
    variable.toString + "(Q" + id.take(4) + ")"
  }
}

object ToInvariantFormVisitor
    extends CollectingVisitor[Stack[String], IExpression]
    with IdGenerator {

  def apply(contractCondition: IExpression): IExpression = {
    visit(contractCondition, Stack[String]())
  }

  override def preVisit(
      t: IExpression,
      quantifierIds: Stack[String]
  ): PreVisitResult = t match {
    case v: IVariableBinder => UniSubArgs(quantifierIds.push(generateId))
    case _                  => KeepArg
  }

  override def postVisit(
      t: IExpression,
      quantifierIds: Stack[String],
      subres: Seq[IExpression]
  ): IExpression = t match {
    case v @ ISortedVariable(index, sort) =>
      if (index < quantifierIds.size) { // quantified variable
        QuantifiedVarWithId(v, quantifierIds(index))
      } else {
        ISortedVariable(index - quantifierIds.size, sort)
      }
    case _ => t update (subres)
  }
}
