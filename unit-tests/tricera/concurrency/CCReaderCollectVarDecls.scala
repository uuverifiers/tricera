package tricera.concurrency

import org.scalatest.flatspec.AnyFlatSpec
import CCReader._
import tricera.params.TriCeraParameters

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
