/**
 * Copyright (c) 2025 Zafer Esen. All rights reserved.
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

package tricera.concurrency.heap

import ap.basetypes.IdealInt
import ap.parser.{IExpression, ITerm}
import IExpression.toFunApplier
import tricera.acsl.ACSLTranslator
import tricera.concurrency.ccreader.CCExceptions.TranslationException
import tricera.concurrency.ccreader._
import tricera.concurrency.concurrent_c.Absyn.{Afunc, Function_def}
import tricera.concurrency.heap.HeapModel._
import tricera.concurrency.heap.InvariantEncodingParser.ParsedEncoding
import tricera.concurrency.{ParseUtil, SymexContext}
import tricera.params.TriCeraParameters

import java.io.StringReader
import java.util.regex.{Matcher, Pattern}
import scala.annotation.tailrec
import scala.collection.mutable

final class InvariantEncodingsFactory(
  context   : SymexContext,
  scope     : CCScope,
  inputVars : Seq[CCVar]) extends HeapModelFactory {

  private val encodingName = TriCeraParameters.get.invEncoding.getOrElse(
    throw new IllegalStateException(
      "InvariantEncodingsFactory created without an encoding type specified.")
  )

  private val originalEncoding : ParsedEncoding =
    InvariantEncodingParser.parse(encodingName)

  private val (transformedInitCode, transformedFunctions) = {
    if (inputVars.isEmpty) {
      (originalEncoding.init_code, Map(
        "$read" -> originalEncoding.read_fn,
        "$write" -> originalEncoding.write_fn,
        "$alloc" -> originalEncoding.alloc_fn,
        "$free" -> originalEncoding.free_fn
        ))
    } else {
      val predNames = originalEncoding.predicates.getOrElse(Nil).map(_.name).toSet

      def transform(code : String) : String =
        transformPredicateCalls(code, predNames, inputVars)

      val newInit = originalEncoding.init_code.map(transform)
      val newFuncs = Map(
        "$read" -> originalEncoding.read_fn.copy(body = transform(originalEncoding.read_fn.body)),
        "$write" -> originalEncoding.write_fn.copy(body = transform(originalEncoding.write_fn.body)),
        "$alloc" -> originalEncoding.alloc_fn.copy(body = transform(originalEncoding.alloc_fn.body)),
        "$free" -> originalEncoding.free_fn.copy(body = transform(originalEncoding.free_fn.body))
        )
      (newInit, newFuncs)
    }
  }

  /**
   * Uses regex to find and prepend arguments to predicate calls in a C code string.
   */
  private def transformPredicateCalls(code          : String,
                                      predNames     : Set[String],
                                      argsToPrepend : Seq[CCVar]) : String = {
    if (argsToPrepend.isEmpty || predNames.isEmpty) return code

    val predPattern = predNames.map(Pattern.quote).mkString("|")
    val regex = s"($predPattern)\\s*\\(([^)]*)\\)".r

    regex.replaceAllIn(code, m => {
      // m.group(1) is the predicate name, e.g., "$R"
      // m.group(2) is the string of existing arguments, e.g., "$cnt, $last_cnt"
      val predName = m.group(1)
      val existingArgs = m.group(2).trim

      // We must escape the predicate name AND the existing arguments,
      // as both are captured from the source and contain literal '$' characters.
      val escapedPredName = Matcher.quoteReplacement(predName)
      val escapedExistingArgs = Matcher.quoteReplacement(existingArgs)

      val argsToPrependString = argsToPrepend.map(_.name).mkString(", ")
      if (existingArgs.isEmpty) {
        s"$escapedPredName($argsToPrependString)"
      } else {
        s"$escapedPredName($argsToPrependString, $escapedExistingArgs)"
      }
    })
  }

  @tailrec
  private def stringToCCType(typeStr    : String,
                             forPointer : Boolean = false)
  : CCType = typeStr match {
    case "int" => CCInt
    case "unsigned int" => CCUInt
    case "void" => CCVoid
    case "PTR_TYPE" if forPointer =>
      throw new TranslationException("PTR_TYPE cannot be nested.")
    case "PTR_TYPE" => stringToCCType(originalEncoding.ptr_type, forPointer = true)
    case "HEAP_TYPE" => CCHeapObject(context.heap)
    case _ => throw new TranslationException(
      s"Unsupported type in encoding file: $typeStr")
  }

  override def requiredVars: Seq[VarSpec] = originalEncoding.global_decls match {
    case Some(decls) => decls.map { decl =>
      val ccType = stringToCCType(decl.`type`)
      val initialValue = decl.initial_value match {
        case Some(v) => ccType match {
          case _: CCArithType => IExpression.i(IdealInt(v))
          case _ => throw new TranslationException(s"Initial value for type ${decl.`type`} not supported.")
        }
        case None => ccType.getNonDet
      }
      VarSpec(decl.name, ccType, isGlobal = true, initialValue)
    }
    case None => Seq()
  }

  override def requiredPreds: Seq[PredSpec] = originalEncoding.predicates match {
    case Some(preds) => preds.map {
      pred =>
        val originalArgs = pred.args.map (arg =>
          new CCVar (arg.name, None, stringToCCType (arg.`type`), AutoStorage))
        PredSpec (pred.name, inputVars ++ originalArgs)
    }
    case None => Seq()
  }

  private def preprocess(code: String): String = {
    val heapObjectReplacement = Matcher.quoteReplacement("$HeapObject")
    code
      .replaceAll("\\bPTR_TYPE\\b", originalEncoding.ptr_type)
      .replaceAll("\\bHEAP_TYPE\\b", heapObjectReplacement) // <-- CORRECTED
      .replaceAll("\\b(HAVOC_INT|HAVOC_HEAP|HEAP_DEFAULT)\\b", "_")
  }

  override def getFunctionsToInject: Map[String, Function_def] = {
    transformedFunctions.map { case (name, funcDef) =>
      val args = funcDef.args.map(a => s"${a.`type`} ${a.name}").mkString(", ")
      val body = if (funcDef.body.trim.isEmpty) ";" else funcDef.body
      val funString = s"${funcDef.return_type} $name($args) { $body }"

      val processedString = preprocess(funString)
      val parsedFunc = ParseUtil.parseFunctionDefinition(
        new StringReader(processedString)).asInstanceOf[Afunc]

      (name, parsedFunc.function_def_)
    }
  }

  override def getInitCodeToInject: Seq[String] = {
    val originalInitCode = {
      val code = transformedInitCode
      if (code.size == 1 && code.head.isEmpty)
        Seq()
      else
        code.map { stmtString =>
          val terminatedStmt = if (stmtString.trim.endsWith(";")) stmtString else stmtString + ";"
          preprocess(terminatedStmt)
        }
    }
    originalInitCode
  }

  override def apply(resources: Resources): HeapModel =
    new InvariantEncodingsModel(context, scope, originalEncoding)
}

class InvariantEncodingsModel(context  : SymexContext,
                              scope    : CCScope,
                              encoding : ParsedEncoding) extends HeapModel{
  private val readFnName  = "$read"
  private val writeFnName = "$write"
  private val allocFnName = "$alloc"
  private val freeFnName  = "$free"

  override def read(p : CCTerm, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult = {
    val resultType = p.typ.asInstanceOf[CCHeapPointer].typ
    val getter = context.sortGetterMap(resultType.toSort)
    FunctionCallWithGetter(
      functionName = readFnName,
      args = Seq(p, loc),
      resultType = resultType,
      getter = getter,
      sourceInfo = p.srcInfo
    )
  }

  override def write(p : CCTerm, o : CCTerm, s : Seq[CCTerm], loc : CCTerm)
  : HeapOperationResult = {
    FunctionCall(
      functionName = writeFnName,
      args = Seq(p, o, loc),
      resultType = CCVoid,
      sourceInfo = p.srcInfo
    )
  }

  override def alloc(o : CCTerm, oType : CCType, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult = {
    FunctionCall(
      functionName = allocFnName,
      args = Seq(o, loc),
      resultType = CCHeapPointer(context.heap, oType),
      sourceInfo = o.srcInfo
    )
  }

  override def free(p : CCTerm, s : Seq[CCTerm], loc : CCTerm) : HeapOperationResult = {
    FunctionCall(
      functionName = freeFnName,
      args = Seq(p, loc),
      resultType = CCVoid,
      sourceInfo = p.srcInfo
    )
  }

  override def getExitAssertions(exitPreds : Seq[CCPredicate]) = Seq()

  // ACSL stuff, these should be refactored to not require a heap term
  override def getACSLPreStateHeapTerm(
    acslContext : ACSLTranslator.FunctionContext) : ITerm = ???
  override def getACSLPostStateHeapTerm(
    acslContext : ACSLTranslator.FunctionContext) : ITerm = ???

  override def batchAlloc(o        : CCTerm,
                          size     : ITerm,
                          arrayLoc : ArrayLocation.Value,
                          s        : Seq[CCTerm]) : HeapOperationResult = {
    ???
  }

  override def arrayRead(arr   : CCTerm,
                         index : CCTerm,
                         s     : Seq[CCTerm],
                         loc   : CCTerm) : HeapOperationResult = {
    ???
  }

  override def arrayWrite(arr   : CCTerm,
                          index : CCTerm,
                          value : CCTerm,
                          s     : Seq[CCTerm],
                          loc   : CCTerm) : HeapOperationResult = {
    ???
  }

  override def allocAndInitArray(arrayPtr         : CCHeapArrayPointer,
                                 size             : ITerm,
                                 initializers     : mutable.Stack[ITerm],
                                 s                : Seq[CCTerm],
                                 loc              : CCTerm) : HeapOperationResult = {
    ???
  }

  override def declUninitializedArray(arrayTyp         : CCHeapArrayPointer,
                                      size             : Option[ITerm],
                                      isGlobalOrStatic : Boolean,
                                      forceNondetInit : Boolean,
                                      s : Seq[CCTerm]) : HeapOperationResult = {
    ???
  }
}