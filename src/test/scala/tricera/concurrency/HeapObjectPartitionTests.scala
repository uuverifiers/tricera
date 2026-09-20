/**
 * Copyright (c) 2026 Zafer Esen. All rights reserved.
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
import lazabs.GlobalParameters
import tricera.params.TriCeraParameters
import tricera.postprocessor.{ACSLContractVerifier, ACSLLinearisedContract}

class HeapObjectPartitionTests extends AnyFlatSpec {

  // struct names in the heap object ADT, and object-wrapper names (O_int, O_H)
  private def partition(program : String) : (Set[String], Set[String]) = {
    val (reader, _, _) = CCReader(
      input         = new java.io.StringReader(program),
      entryFunction = "main")
    (reader.structCtorSignatures.map(_._1).toSet,
     reader.wrapperSignatures.map(_._1).toSet)
  }

  private val O_int = "O_" + CCInt.shortName

  "A value-only struct" should "stay out of the heap object ADT" in {
    val (heapStructs, _) = partition(
      """
        |struct V { int a; };
        |struct H { int b; };
        |void main() {
        |  struct V v;
        |  v.a = 5;
        |  struct H *h = calloc(sizeof(struct H));
        |  h->b = v.a;
        |  assert(h->b == 5);
        |}
        |""".stripMargin)
    assert(heapStructs.contains("H"))
    assert(!heapStructs.contains("V"))
  }

  "A value struct nested in a heap struct" should
    "be pulled into the heap object ADT" in {
    val (heapStructs, _) = partition(
      """
        |struct Inner { int x; };
        |struct Outer { struct Inner in; int y; };
        |void main() {
        |  struct Outer *o = calloc(sizeof(struct Outer));
        |  o->y = 1;
        |  assert(o->y == 1);
        |}
        |""".stripMargin)
    assert(heapStructs.contains("Outer"))
    assert(heapStructs.contains("Inner"))
  }

  "A struct both heap-allocated and nested by value" should
    "pull its value container into the heap object ADT" in {
    val (heapStructs, _) = partition(
      """
        |struct J { int x; };
        |struct I { struct J j; };
        |void main() {
        |  struct J *pj = calloc(sizeof(struct J));
        |  pj->x = 7;
        |  struct I iv;
        |  iv.j.x = pj->x;
        |  assert(iv.j.x == 7);
        |}
        |""".stripMargin)
    assert(heapStructs.contains("J"))
    assert(heapStructs.contains("I"))
  }

  "Pure value structs" should "stay standalone even when a heap is modelled" in {
    val (heapStructs, _) = partition(
      """
        |struct A { int x; };
        |struct B { struct A a; };
        |void main() {
        |  int *p = calloc(sizeof(int));
        |  *p = 3;
        |  struct B b;
        |  b.a.x = *p;
        |  assert(b.a.x == 3);
        |}
        |""".stripMargin)
    assert(!heapStructs.contains("A"))
    assert(!heapStructs.contains("B"))
  }

  "An int used only inside structs" should "not get an object wrapper" in {
    val (_, wrappers) = partition(
      """
        |struct H { int b; };
        |void main() {
        |  struct H *h = calloc(sizeof(struct H));
        |  h->b = 5;
        |  assert(h->b == 5);
        |}
        |""".stripMargin)
    assert(wrappers.contains("O_H"))
    assert(!wrappers.contains(O_int))
  }

  "An int allocated on the heap" should "get an object wrapper" in {
    val (_, wrappers) = partition(
      """
        |void main() {
        |  int *p = calloc(sizeof(int));
        |  *p = 3;
        |  assert(*p == 3);
        |}
        |""".stripMargin)
    assert(wrappers.contains(O_int))
  }

  private def withHeapReaders(program : String)(test : CCReader => Unit) : Unit =
    for (heap <- Seq(TriCeraParameters.NativeHeap, TriCeraParameters.ArrayHeap)) {
      val params = new TriCeraParameters
      params.heapModel = heap
      TriCeraParameters.parameters.withValue(params) {
        GlobalParameters.withValue(params) {
          val input = program.replace("/*@contract@*/", "■■contract■■")
          val (reader, _, _) = CCReader(new java.io.StringReader(input), "main")
          test(reader)
        }
      }
    }

  "Contract verification" should "require valid accesses through callees" in {
    withHeapReaders("""
      |/*@contract@*/ int read_cell(int *p) { return *p; }
      |/*@contract@*/ int get(int *p) { return read_cell(p); }
      |void main() { int *p = malloc(sizeof(int)); *p = 7; get(p); }
      |""".stripMargin) { reader =>
      val verifier = new ACSLContractVerifier(reader)
      val contract = ACSLLinearisedContract("get", "\\valid(p)",
        "\\result == *p", Nil, Some("\\nothing"))
      assert(verifier.verify(contract, 10000))
      assert(!verifier.verify(contract.copy(preCondition = "\\true"), 10000))
      assert(!verifier.verify(contract.copy(postCondition = "\\result == *p + 1"), 10000))
    }
  }

  it should "check frees without changing the main encoding" in {
    withHeapReaders("""
      |/*@contract@*/ void release(int *p) { free(p); }
      |void main() { int *p = malloc(sizeof(int)); release(p); assert(0); }
      |""".stripMargin) { reader =>
      val system = reader.system
      val before = (system.processes, system.assertions, system.backgroundAxioms,
        reader.wrapperSignatures, CCReader.forcedObjectWrapperTypes.toVector)
      val verifier = new ACSLContractVerifier(reader)
      val contract = ACSLLinearisedContract("release", "\\valid(p)", "\\true", Nil)
      assert(verifier.verify(contract, 10000))
      assert(!verifier.verify(contract.copy(preCondition = "\\true"), 10000))
      assert(before == ((system.processes, system.assertions, system.backgroundAxioms,
        reader.wrapperSignatures, CCReader.forcedObjectWrapperTypes.toVector)))
    }
  }

  it should "check array bounds even for a live neighbouring cell" in {
    withHeapReaders("""
      |int a[2], b[2];
      |/*@contract@*/ int get(int n) { return a[n]; }
      |void main() { b[0] = 3; get(1); assert(b[0] == 3); }
      |""".stripMargin) { reader =>
      val verifier = new ACSLContractVerifier(reader)
      val contract = ACSLLinearisedContract("get", "0 <= n && n < 2", "\\true", Nil)
      assert(verifier.verify(contract, 10000))
      assert(!verifier.verify(contract.copy(preCondition = "n == 2"), 10000))
    }
  }

  it should "preserve globals omitted from assigns" in {
    withHeapReaders("""
      |int count, unchanged;
      |/*@contract@*/ void increment(int *p) { ++count; ++*p; }
      |void main() { int *p = malloc(sizeof(int)); *p = 0; increment(p); }
      |""".stripMargin) { reader =>
      val verifier = new ACSLContractVerifier(reader)
      val contract = ACSLLinearisedContract("increment", "\\valid(p)",
        "count == \\old(count) + 1 && *p == \\old(*p) + 1", Nil,
        Some("count, *p"))
      assert(verifier.verify(contract, 10000))
      assert(!verifier.verify(contract.copy(assigns = Some("*p")), 10000))
      assert(!verifier.verify(contract.copy(assigns = Some("count")), 10000))
    }
  }
}
