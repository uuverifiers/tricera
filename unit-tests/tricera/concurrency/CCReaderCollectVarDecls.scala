/**
 * Copyright (c) 2022-2023 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import org.scalatest.flatspec.AnyFlatSpec
import CCReader._
import ccreader._
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

  val (reader, modelledHeap) = CCReader(input = testFileReader,
                                        entryFunction = "main")

  private def testCollectVarDeclsNoInit(dec : String,
                                        isGlobal : Boolean,
                                        expected : CCType) : Boolean = {
    val decl = Util.parseGlobalDeclaration(new java.io.StringReader(dec))
    reader.collectVarDecls(decl, isGlobal = isGlobal) match {
      case Seq(reader.CCVarDeclaration(_, `expected`, _, _, _, _, _, _, _)) => true
      case _ => false
    }
  }

////////////////////////////////////////////////////////////////////////////////
// Tests
  "The type of int x" should "be int" in {
    assert(testCollectVarDeclsNoInit(dec = "int x;",
                              isGlobal = true,
                              expected = CCInt))
  }

  "The type of int *x" should "be int*" in {
    assert(testCollectVarDeclsNoInit(dec = "int *x;",
      isGlobal = true,
      expected = CCHeapPointer(reader.heap, CCInt)))
  }

  "The type of int **x" should "be int**" in {
    assert(testCollectVarDeclsNoInit(dec = "int **x;",
      isGlobal = true,
      expected = CCHeapPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt))))
  }

  "The type of global int a[10]" should "be global array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[10];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap, CCInt,
                                    ArrayLocation.Global)))
  }

  "The type of local int a[10]" should "be stack array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[10];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap, CCInt,
                                    ArrayLocation.Stack)))
  }

  "The type of local int a[]" should "be heap array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap, CCInt,
                                    ArrayLocation.Heap)))
  }

  "The type of global int a[]" should "be heap array of ints" in {
    assert(testCollectVarDeclsNoInit("int a[];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap, CCInt,
                                    ArrayLocation.Heap)))
  }

  "The type of global int *a[10]" should "be global array of int pointers" in {
    assert(testCollectVarDeclsNoInit("int *a[10];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt), ArrayLocation.Global)))
  }

  "The type of local int *a[10]" should "be stack array of int pointers" in {
    assert(testCollectVarDeclsNoInit("int *a[10];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt), ArrayLocation.Stack)))
  }

  "The type of local int *a[]" should "be heap array of int pointers" in {
    assert(testCollectVarDeclsNoInit("int *a[];",isGlobal = false,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCInt), ArrayLocation.Heap)))
  }

  "The type of global int **a[10]" should "be global array of int**" in {
    assert(testCollectVarDeclsNoInit("int **a[10];",isGlobal = true,
      expected = CCHeapArrayPointer(reader.heap,
        CCHeapPointer(reader.heap, CCHeapPointer(reader.heap, CCInt)),
                                    ArrayLocation.Global)))
  }

}
