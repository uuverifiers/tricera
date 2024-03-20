  
package tricera.concurrency

import ap.parser._
import ap.theories.rationals.Rationals
import ap.theories.{ADT}
import ap.types.{MonoSortedIFunction}

  //////////////////////////////////////////////////////////////////////////////
  // Long Doubles
  object LongDoubleADT {
    private val longDoubleADTCtorSignatures: Seq[(String, ADT.CtorSignature)] = Seq(
      ("longDoubleData", ADT.CtorSignature(
        Seq(("getLongDouble", ADT.OtherSort(Rationals.dom))), ADT.ADTSort(0))),
      ("NaN", ADT.CtorSignature(Nil, ADT.ADTSort(0))),
      ("plusInfinity", ADT.CtorSignature(Nil, ADT.ADTSort(0))),
      ("negativeInfinity", ADT.CtorSignature(Nil, ADT.ADTSort(0)))
    )

    val longDoubleADT = new ADT(sortNames = Seq("longDoubleADT"),
      longDoubleADTCtorSignatures)
    val sort = longDoubleADT.sorts.head

    val longDoubleCtor: MonoSortedIFunction = longDoubleADT.constructors(0)
    val getData: MonoSortedIFunction = longDoubleADT.selectors(0)(0)

    val nan: ITerm = IFunApp(longDoubleADT.constructors(1), Nil)
    val plusInf: ITerm = IFunApp(longDoubleADT.constructors(2), Nil)
    val negInf: ITerm = IFunApp(longDoubleADT.constructors(3), Nil)

    def isFloat(t: ITerm): IFormula = longDoubleADT.hasCtor(t, 0)

    def isNan(t: ITerm): IFormula = longDoubleADT.hasCtor(t, 1)

    def isPlusinf(t: ITerm): IFormula = longDoubleADT.hasCtor(t, 2)

    def isNeginf(t: ITerm): IFormula = longDoubleADT.hasCtor(t, 3)
  }

  object LongDoubles {

    import scala.util.control._
    import scala.math._

    // todo: uses the same implementation as Doubles right now. Should be fixed
    def longDoubleToFraction(fp: String): (String, String) = {
      val f: Double = fp.toDouble
      println("Warning: wrong implementation for converting Long Doubles to Doubles")
      if (f.isNaN) {
        ("0", "0")
      }
      else if (f.isInfinity) {
        ("0", "0")
      }
      else {
        val mantissaBits: Long = (java.lang.Double.doubleToLongBits(f) << 12 >>> 12)
        val mantissa: String = String.format("%52s", java.lang.Long.toBinaryString(mantissaBits)).replace(' ', '0')

        val exponentBits: Long = (java.lang.Double.doubleToLongBits(f) << 1 >>> 53)
        val exponent: String = String.format("%11s", java.lang.Long.toBinaryString(exponentBits)).replace(' ', '0')

        val signBit = (java.lang.Double.doubleToLongBits(f) >>> 63).toBinaryString

        var bitCount: Int = 53
        var denominator: BigInt = 1
        var numerator: BigInt = 0

        //Get the denominator from the mantissa
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
        //Get the numerator from the mantissa
        for (bit <- mantissa) {
          if (bit == '1') {
            numerator = numerator + denominator / BigInt(2).pow(bitCount)
          }
          bitCount = bitCount + 1
        }

        bitCount = 0
        // Get the exponent
        var exponentInt: Int = -pow(2, exponent.length() - 1).toInt + 1
        for (bit <- exponent.reverse) {
          if (bit == '1') {
            exponentInt = exponentInt + pow(2, bitCount).toInt
          }
          bitCount = bitCount + 1
        }

        if (exponentInt > 0) {
          numerator = numerator * BigInt(2).pow(exponentInt)
        }
        if (exponentInt < 0) {
          denominator = denominator * BigInt(2).pow(abs(exponentInt))
        }
        // Case for when the float is 0
        if (exponentInt == -pow(2, exponent.length() - 1).toInt + 1 && numerator == 1) {
          numerator = 0
          denominator = 1
        }
        if (signBit == "1") {
          numerator = -numerator
        }
        (numerator.toString, denominator.toString)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Doubles
  object DoubleADT {
    private val doubleADTCtorSignatures: Seq[(String, ADT.CtorSignature)] = Seq(
      ("doubleData", ADT.CtorSignature(
        Seq(("getDouble", ADT.OtherSort(Rationals.dom))), ADT.ADTSort(0))),
      ("NaN", ADT.CtorSignature(Nil, ADT.ADTSort(0))),
      ("plusInfinity", ADT.CtorSignature(Nil, ADT.ADTSort(0))),
      ("negativeInfinity", ADT.CtorSignature(Nil, ADT.ADTSort(0)))
    )

    val doubleADT = new ADT(sortNames = Seq("doubleADT"),
      doubleADTCtorSignatures)
    val sort = doubleADT.sorts.head

    val doubleCtor: MonoSortedIFunction = doubleADT.constructors(0)
    val getData: MonoSortedIFunction = doubleADT.selectors(0)(0)

    val nan: ITerm = IFunApp(doubleADT.constructors(1), Nil)
    val plusInf: ITerm = IFunApp(doubleADT.constructors(2), Nil)
    val negInf: ITerm = IFunApp(doubleADT.constructors(3), Nil)

    def isFloat(t: ITerm): IFormula = doubleADT.hasCtor(t, 0)

    def isNan(t: ITerm): IFormula = doubleADT.hasCtor(t, 1)

    def isPlusinf(t: ITerm): IFormula = doubleADT.hasCtor(t, 2)

    def isNeginf(t: ITerm): IFormula = doubleADT.hasCtor(t, 3)
  }

  object Doubles {
    import scala.util.control._
    import scala.math._
    def doubleToFraction(fp: String): (String, String) = {
    val f: Double = fp.toDouble
    if (f.isNaN) {
      ("0", "0")
    }
    else if (f.isInfinity) {
      ("1", "0")
    }
    else {
      val mantissaBits: Long = (java.lang.Double.doubleToLongBits(f) << 12 >>> 12)
      val mantissa: String = String.format("%52s", java.lang.Long.toBinaryString(mantissaBits)).replace(' ', '0')

      val exponentBits: Long = (java.lang.Double.doubleToLongBits(f) << 1 >>> 53)
      val exponent: String = String.format("%11s", java.lang.Long.toBinaryString(exponentBits)).replace(' ', '0')

      val signBit = (java.lang.Double.doubleToLongBits(f) >>> 63).toBinaryString

      var bitCount: Int = 53
      var denominator: BigInt = 1
      var numerator: BigInt = 0

      //Get the denominator from the mantissa
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
      //Get the numerator from the mantissa
      for (bit <- mantissa) {
        if (bit == '1') {
          numerator = numerator + denominator / BigInt(2).pow(bitCount)
        }
        bitCount = bitCount + 1
      }

      bitCount = 0
      // Get the exponent
      var exponentInt: Int = -pow(2, exponent.length() - 1).toInt + 1
      for (bit <- exponent.reverse) {
        if (bit == '1') {
          exponentInt = exponentInt + pow(2, bitCount).toInt
        }
        bitCount = bitCount + 1
      }

      if (exponentInt > 0) {
        numerator = numerator * BigInt(2).pow(exponentInt)
      }
      if (exponentInt < 0) {
        denominator = denominator * BigInt(2).pow(abs(exponentInt))
      }
      // Case for when the float is 0
      if (exponentInt == -pow(2, exponent.length() - 1).toInt + 1 && numerator == 1) {
        numerator = 0
        denominator = 1
      }
      if (signBit == "1") {
        numerator = -numerator
      }
      (numerator.toString, denominator.toString)
    }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Floats
  object FloatADT {
    private val floatADTCtorSignatures : Seq[(String, ADT.CtorSignature)] = Seq(
      ("floatData", ADT.CtorSignature(
        Seq(("getFloat", ADT.OtherSort(Rationals.dom))), ADT.ADTSort(0))),
      ("NaN", ADT.CtorSignature(Nil, ADT.ADTSort(0))),
      ("plusInfinity", ADT.CtorSignature(Nil, ADT.ADTSort(0))),
      ("negativeInfinity", ADT.CtorSignature(Nil, ADT.ADTSort(0)))
    )

    val floatADT     = new ADT(sortNames = Seq("floatADT"),
                               floatADTCtorSignatures)
    val sort = floatADT.sorts.head

    val floatCtor : MonoSortedIFunction = floatADT.constructors(0)
    val getData   : MonoSortedIFunction = floatADT.selectors(0)(0)

    val nan     : ITerm = IFunApp(floatADT.constructors(1), Nil)
    val plusInf : ITerm = IFunApp(floatADT.constructors(2), Nil)
    val negInf  : ITerm = IFunApp(floatADT.constructors(3), Nil)

    // val isFloat   : Predicate = floatADT.ctorIdPreds(0)

    def isFloat(t: ITerm): IFormula = floatADT.hasCtor(t, 0)
    def isNan(t: ITerm): IFormula = floatADT.hasCtor(t, 1)
    def isPlusinf(t: ITerm): IFormula = floatADT.hasCtor(t, 2)
    def isNeginf(t: ITerm): IFormula = floatADT.hasCtor(t, 3)

    // val isFloat   : Predicate = floatADT.hasCtor(I, 0)
    // val isNan     : Predicate = floatADT.ctorIdPreds(1)
    // val isPlusInf : Predicate = floatADT.ctorIdPreds(2)
    // val isNegInf  : Predicate = floatADT.ctorIdPreds(3)
  }

  object Floats {

    import scala.util.control._
    import scala.math._
    def floatToFraction(fp: String): (String, String) = {
      val f: Float = fp.toFloat

      if (f.isNaN) {
        ("0", "0")
      }
      else if (f.isInfinity) {
        ("0", "0")
      }
      else {
        //
        val mantissaBits: Int = java.lang.Float.floatToIntBits(f) << 9 >>> 9
        val mantissa: String = String.format("%23s", Integer.toBinaryString(mantissaBits)).replace(' ', '0')

        val exponentBits: Int = (java.lang.Float.floatToIntBits(f) << 1 >>> 24)
        val exponent: String = String.format("%8s", Integer.toBinaryString(exponentBits)).replace(' ', '0')

        val signBit = (java.lang.Float.floatToIntBits(f) >>> 31).toBinaryString

        var bitCount: Int = 23

        var denominator: BigInt = 1
        var numerator: BigInt = 0
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
        // Case for when the float is 0
        if (exponentInt == -pow(2, exponent.length() - 1).toInt + 1 && numerator == 1){
          numerator = 0
          denominator = 1
        }
        if (signBit == "1") {
          numerator = -numerator
        }
        (numerator.toString, denominator.toString)
      }
    }
  }

