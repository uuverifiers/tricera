package tricera.concurrency

import ap.theories.ADT
import org.scalatest.flatspec.AnyFlatSpec
import tricera.postprocessor.ADTSimplifier
import ap.types.Sort
import ap.theories.bitvectors.ModuloArithmetic._

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

  "ADTSimplifier" should "extract y when the constructor is nested in the selector" in {
    val simplifier = new ADTSimplifier()
    val form = IFuncApp()
  }
}
