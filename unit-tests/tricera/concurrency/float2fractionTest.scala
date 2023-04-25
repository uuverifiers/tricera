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
import tricera.concurrency.CCReader.Floats._
class FractionTest extends AnyFlatSpec {
  // create a dummy file to create an instance of CCReader

  ////////////////////////////////////////////////////////////////////////////////
  // Tests
  var foo: (String, String) = float2fraction("2.0f")
  assert(foo == ("2", "1"))

  foo = float2fraction("-2.0f")
  assert(foo == ("-2", "1"))

  foo = float2fraction("8.0f")
  assert(foo == ("8", "1"))

  foo = float2fraction("-8.0f")
  assert(foo == ("-8", "1"))

  foo = float2fraction("3.14f")
  assert(foo == ("26340230", "8388608"))

  foo = float2fraction("-3.14f")
  assert(foo == ("-26340230", "8388608"))

  foo = float2fraction("2.64f")
  assert(foo == ("22145926", "8388608"))

  foo = float2fraction("-2.64f")
  assert(foo == ("-22145926", "8388608"))

  foo = float2fraction("0.125f")
  assert(foo == ("1", "8"))

  foo = float2fraction("-0.125f")
  assert(foo == ("-1", "8"))

  foo = float2fraction("0.0032f")
  assert(foo == ("13743895", "4294967296"))

  foo = float2fraction("-0.0032f")
  assert(foo == ("-13743895", "4294967296"))

  foo = float2fraction("0.69f")
  assert(foo == ("11576279", "16777216"))

  foo = float2fraction("-0.69f")
  assert(foo == ("-11576279", "16777216"))

  foo = float2fraction("2.35098856151e-38")
  assert(foo == ("16777215" , "713623846352979940529142984724747568191373312"))

  foo = float2fraction("-2.35098856151e-38")
  assert(foo == ("-16777215", "713623846352979940529142984724747568191373312"))

  println("ALL TESTS PASSED")
}
