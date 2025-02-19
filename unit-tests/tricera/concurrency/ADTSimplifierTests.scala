package tricera.concurrency

import org.scalatest.flatspec.AnyFlatSpec

import ap.theories.ADT
import ap.types.Sort
import ap.parser._
import ap.theories.bitvectors.ModuloArithmetic._

import tricera.postprocessor.ADTSimplifier
import ap.terfor.ConstantTerm
import tricera.{FunctionInvariants, Invariant, PostCondition, PreCondition, Result, Solution}
import ap.types.MonoSortedIFunction
import ap.theories.TheoryRegistry


class ADTSimplifierTests extends AnyFlatSpec {
  val adtSimplifierTestsADTs = {
    // This registers an ADT corresponding to a simple C struct
    //
    // struct Simple {
    //   int x;
    //   unsigned int y;
    // }
    val simpleSort = ADT.ADTSort(0)
    new ADT(
      Seq("Simple"),
      Seq(("Simple", ADT.CtorSignature(
        Seq(("x", ADT.OtherSort(SignedBVSort(32))),
            ("y", ADT.OtherSort(UnsignedBVSort(32)))),
        simpleSort)))
    )
  }

  val simpleCtor = adtSimplifierTestsADTs.constructors(0)
  val xSelector = adtSimplifierTestsADTs.selectors(0)(0)
  val ySelector = adtSimplifierTestsADTs.selectors(0)(1)
  val xValue = IConstant(new ConstantTerm("x-value"))
  val yValue = IConstant(new ConstantTerm("y-value"))
  val someValue = IConstant(new ConstantTerm("someValue"))
  val someFunction = new IFunction("someFunction", 2, false, false)

  def makeSolution(form: IFormula) = {
    Solution(Seq(
      FunctionInvariants(
        "someId",
        false, 
        PreCondition(Invariant(form, None, None)),
        PostCondition(Invariant(form, None, None)),
        List())))
  }

  "ADTSimplifier" should "extract a value when a constructor is nested within a selector" in {
    val form = IEquation(
      IFunApp(ySelector, Seq(IFunApp(simpleCtor, Seq(xValue, yValue)))),
      someValue)

    val expected = IEquation(yValue, someValue)

    ADTSimplifier(makeSolution(form)) match {
      case Solution(Seq(functionInvariants)) => 
        assert(functionInvariants.preCondition.invariant.expression == expected)
        assert(functionInvariants.postCondition.invariant.expression == expected)
      case _ => fail("Result was of unexpected type")
    }
  }

  "ADTSimplifier" should "leave the expression alone in any other case" in {
    // NOTE: Testing "any other case" is hard, but this is one example
    val form = IEquation(
      IFunApp(ySelector, Seq(IFunApp(someFunction, Seq(xValue, yValue)))),
      someValue)
    
    val expected = form

    ADTSimplifier(makeSolution(form)) match {
      case Solution(Seq(functionInvariants)) => 
        assert(functionInvariants.preCondition.invariant.expression == expected)
        assert(functionInvariants.postCondition.invariant.expression == expected)
      case _ => fail("Result was of unexpected type")
    }

  }
}
