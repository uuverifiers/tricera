package tricera.concurrency

import org.scalatest.flatspec.AnyFlatSpec
import CCReader._

import scala.util.control._
import scala.math.BigInt
import  scala.math._
import java.math.BigInteger
import org.scalatest._

import scala.math.BigDecimal.int2bigDecimal

class toFractionTests extends AnyFlatSpec {
  // create a dummy file to create an instance of CCReader
  val testFileReader = new java.io.StringReader(
    """
      |void main(){
      |}
      |""".stripMargin
  )

  // arithmetic mode must be implicitly declared for the correct types
  // would need to be changed or scoped to test different arith. modes
  implicit def arithMode = tricera.params.TriCeraParameters.get.arithMode

  val (reader, modelledHeap) = CCReader(input = testFileReader,
    entryFunction = "main")


  def float2fractionTest(fp: String): (String, String) = {
    val f: Float = fp.toFloat

    if (f.isNaN) {
      ("0", "0")
    }
    else if (f.isInfinity) {
      ("0", "0")
    }
    else {
      //
      val mantissaBits: Int = java.lang.Float.floatToIntBits(f) << 8 >>> 8
      val mantissa: String = String.format("%23s", Integer.toBinaryString(mantissaBits)).replace(' ', '0')

      val exponentBits: Int = (java.lang.Float.floatToIntBits(f) << 1 >>> 24)
      val exponent: String = String.format("%8s", Integer.toBinaryString(exponentBits)).replace(' ', '0')

      val signBit = (java.lang.Float.floatToIntBits(f) >>> 31).toBinaryString

      var bitCount: Int = 23

      var denominator: BigInt = 1
      var numerator : BigInt = 0
      var loop = new Breaks
      loop.breakable {
        for (bit <- mantissa.reverse) {
          if (bit == '1') {
            denominator = BigInt(2).pow(bitCount)
            loop.break()
          }
          bitCount = bitCount - 1
        }
      }

      // reset bitCount
      bitCount = 1
      numerator = denominator
      for (bit <- mantissa) {
        if (bit == '1') {
          numerator = numerator + denominator / BigInt(2).pow(bitCount)
      }
        bitCount = bitCount + 1
      }

      bitCount = 0
      var exponentInt: Int = -pow(2, exponent.length() - 1).toInt + 1
      for (bit <- exponent.reverse) {
        if (bit == '1') {
          exponentInt = exponentInt + pow(2, bitCount).toInt
        }
        bitCount = bitCount + 1
      }
denominator
      if (exponentInt > 0) {
        numerator = numerator * BigInt(2).pow(exponentInt)
      }
      if (exponentInt < 0) {
        denominator = denominator * BigInt(2).pow(abs(exponentInt))
      }
      if (signBit == "1") {
        numerator = -numerator
      }
      (numerator.toString, denominator.toString)
    }
  }

  ////////////////////////////////////////////////////////////////////////////////
  // Tests
  var foo : (String, String) = float2fractionTest("2.0f")
  assert(foo == ("2", "1"))

  foo = float2fractionTest("-2.0f")
  assert(foo == ("-2", "1"))

  foo = float2fractionTest("8.0f")
  assert(foo == ("8", "1"))

  foo = float2fractionTest("-8.0f")
  assert(foo == ("-8", "1"))

  foo = float2fractionTest("3.14f")
  assert(foo == ("26340230","8388608"))

  foo = float2fractionTest("-3.14f")
  assert(foo == ("-26340230", "8388608"))

  foo = float2fractionTest("2.64f")
  assert(foo == ("22145926", "8388608"))

  foo = float2fractionTest("-2.64f")
  assert(foo == ("-22145926", "8388608"))

  foo = float2fractionTest("0.125f")
  assert(foo == ("1", "8"))

  foo = float2fractionTest("-0.125f")
  assert(foo == ("-1", "8"))

  foo = float2fractionTest("0.0032f")
  assert(foo == ("13743895", "4294967296"))

  foo = float2fractionTest("-0.0032f")
  assert(foo == ("-13743895", "4294967296"))

  foo = float2fractionTest("0.69f")
  assert(foo == ("11576279", "16777216"))

  foo = float2fractionTest("-0.69f")
  assert(foo == ("-11576279", "16777216"))


}
class CCReaderCollectVarDecls extends AnyFlatSpec {
////////////////////////////////////////////////////////////////////////////////
// Configuration

  // create a dummy file to create an instance of CCReader
  val testFileReader = new java.io.StringReader(
    """
      |void main(){
      |}
      |""".stripMargin
  )

  // arithmetic mode must be implicitly declared for the correct types
  // would need to be changed or scoped to test different arith. modes
  implicit def arithMode = tricera.params.TriCeraParameters.get.arithMode

  val (reader, modelledHeap) = CCReader(input = testFileReader,
                                        entryFunction = "main")

  private def testCollectVarDeclsNoInit(dec : String,
                                        isGlobal : Boolean,
                                        expected : CCType) : Boolean = {
    val decl = Util.parseGlobalDeclaration(new java.io.StringReader(dec))
    reader.collectVarDecls(decl, isGlobal = isGlobal) match {
      case Seq(reader.CCVarDeclaration(_, `expected`, _, _, _, _, _, _)) => true
      case _ => false
    }
  }

////////////////////////////////////////////////////////////////////////////////
// Tests
  "The type of int x" should "be int" in {
    assert(testCollectVarDeclsNoInit(dec = "int x;",
                              isGlobal = true,
                              expected = CCInt()))
  }

  "The type of int *x" should "be int*" in {
    assert(testCollectVarDeclsNoInit(dec = "int *x;",
      isGlobal = true,
      expected = CCHeapPointer(reader.heap, CCInt())))
  }

  "The type of int **x" should "be int**" in {
    assert(testCollectVarDeclsNoInit(dec = "int **x;",
      isGlobal = true,
      expected = CCHeapPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt()))))
  }

  "The type of global int a[10]" should "be global array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[10];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap, CCInt(),
                                    ArrayLocation.GlobalArray)))
  }

  "The type of local int a[10]" should "be stack array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[10];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap, CCInt(),
                                    ArrayLocation.StackArray)))
  }

  "The type of local int a[]" should "be heap array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap, CCInt(),
                                    ArrayLocation.HeapArray)))
  }

  "The type of global int a[]" should "be heap array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap, CCInt(),
                                    ArrayLocation.HeapArray)))
  }

  "The type of global int *a[10]" should "be global array of int pointers" in {
    assert(testCollectVarDeclsNoInit("int *a[10];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt()), ArrayLocation.GlobalArray)))
  }

  "The type of local int *a[10]" should "be stack array of int pointers" in {
    assert(testCollectVarDeclsNoInit("int *a[10];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt()), ArrayLocation.StackArray)))
  }

  "The type of local int *a[]" should "be heap array of int pointers" in {
    assert(testCollectVarDeclsNoInit("int *a[];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt()), ArrayLocation.HeapArray)))
  }

  "The type of global int **a[10]" should "be global array of int**" in {
    assert(testCollectVarDeclsNoInit("int **a[10];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCHeapPointer(reader.heap, CCInt())),
                                    ArrayLocation.GlobalArray)))
  }

}
