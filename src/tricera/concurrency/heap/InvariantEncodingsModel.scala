package tricera.concurrency.heap

import ap.basetypes.IdealInt
import ap.parser.IExpression.toFunApplier
import ap.parser.{IExpression, IFunApp, IFunction, ITerm}
import ap.types.MonoSortedIFunction
import tricera.acsl.ACSLTranslator
import tricera.concurrency.ccreader.CCExceptions.TranslationException
import tricera.concurrency.ccreader._
import tricera.concurrency.concurrent_c.Absyn.{Afunc, Function_def}
import tricera.concurrency.heap.HeapModel._
import tricera.concurrency.heap.InvariantEncodingParser.{
  Argument,
  ParsedEncoding
}
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
      val predNames = originalEncoding.predicates.map(_.name).toSet

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

//  private val encoding : ParsedEncoding = createModifiedEncoding()

//  private def createModifiedEncoding(): ParsedEncoding = {
//    val original = InvariantEncodingParser.parse(encodingName)
//    if (inputVars.isEmpty) {
//      return original // No transformation needed, return early.
//    }
//
//    val argsToPrependStr = inputVars.map(_.name).mkString(", ")
//
//    val inputArgs : List[Argument] = inputVars.map { ccVar =>
//      val typeStr = ccVar.typ match {
//        case _: CCInvariantPointer => "PTR_TYPE"
//        case _: CCHeapObject       => "HEAP_TYPE"
//        case CCInt                 => "int"
//        case CCUInt                => "unsigned int"
//        case t                     => t.shortName
//      }
//      Argument(ccVar.name, typeStr)
//    }.toList
//
//    val newPredicates = original.predicates.map { pred =>
//      pred.copy(args = inputArgs ++ pred.args)
//    }
//    val predNamesToTransform = original.predicates.map(_.name).toSet
//
//    def transformCalls(code: String): String = {
//      transformPredicateCalls(code, predNamesToTransform, argsToPrependStr)
//    }
//
//    val newInitCode = original.init_code.map(transformCalls)
//    val newReadFn   = original.read_fn.copy(body = transformCalls(original.read_fn.body))
//    val newWriteFn  = original.write_fn.copy(body = transformCalls(original.write_fn.body))
//    val newAllocFn  = original.alloc_fn.copy(body = transformCalls(original.alloc_fn.body))
//    val newFreeFn   = original.free_fn.copy(body = transformCalls(original.free_fn.body))
//
//    original.copy(
//      predicates = newPredicates,
//      init_code  = newInitCode,
//      read_fn    = newReadFn,
//      write_fn   = newWriteFn,
//      alloc_fn   = newAllocFn,
//      free_fn    = newFreeFn
//      )
//  }

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

override def requiredVars: Seq[VarSpec] = {
    originalEncoding.global_decls.map { decl =>
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
  }

  override def requiredPreds: Seq[PredSpec] =
    originalEncoding.predicates.map { pred =>
      val originalArgs = pred.args.map(arg =>
        new CCVar(arg.name, None, stringToCCType(arg.`type`), AutoStorage))
      PredSpec(pred.name, inputVars ++ originalArgs)
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
    // First initialize the input variables added by tri-pp to nondet,
    // this must happen first to fix their values, as other init statements
    // might rely on their values (e.g., an assume/assert over the invariants).
    val nonDetInits = inputVars.map(v => s"${v.name} = _;")

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

    nonDetInits ++ originalInitCode
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

  private def getObjectType(p : CCExpr) : CCType = p.typ match {
    case CCInvariantPointer(_, objT) => objT
    case _ => throw new TranslationException("Expected an invariant heap pointer type.")
  }

  override def read(p : CCExpr, s : Seq[CCExpr]) : HeapOperationResult = {
    val getter = context.sortGetterMap(
      p.typ.asInstanceOf[CCInvariantPointer].elementType.toSort)
    FunctionCallWithGetter(
      functionName = readFnName,
      args = Seq(p),
      resultType = getObjectType(p),
      getter = getter,
      sourceInfo = p.srcInfo
    )
  }

  override def write(p : CCExpr, o : CCExpr, s : Seq[CCExpr])
  : HeapOperationResult = {
    FunctionCall(
      functionName = writeFnName,
      args = Seq(p, o),
      resultType = CCVoid,
      sourceInfo = p.srcInfo
    )
  }

  override def alloc(o : CCTerm, s : Seq[CCExpr]) : HeapOperationResult = {
    FunctionCall(
      functionName = allocFnName,
      args = Seq(o),
      resultType = CCInvariantPointer(context.heap, o.typ),
      sourceInfo = o.srcInfo
    )
  }

  override def free(p : CCExpr, s : Seq[CCExpr]) : HeapOperationResult = {
    FunctionCall(
      functionName = freeFnName,
      args = Seq(p),
      resultType = CCVoid,
      sourceInfo = p.srcInfo
    )
  }

// In class InvariantEncodingsModel...

  override def write(rootPointer : CCTerm,
                     lhs         : IFunApp,
                     rhs         : CCExpr,
                     s           : Seq[CCExpr]) : HeapOperationResult = {
    rootPointer.typ match {
      case typ : CCInvariantPointer =>
        typ.elementType match {
          case structType: CCStruct =>
            // `lhs` is the term for the field, e.g., `left_selector(struct_getter(...))`
            val fieldSelector = lhs.fun
            val oldStructObjectTerm = lhs.args.head // The term for the old struct object.

            val constructor = structType.ctor
            val allSelectors = structType.sels
            val updatedSelectorIndex = allSelectors.indexWhere(p => p._1 == fieldSelector)

            if (updatedSelectorIndex == -1) {
              throw new TranslationException(s"Internal error: could not find selector ${
                fieldSelector.name} in struct ${structType.shortName}")
            }

            val constructorArgs = for (i <- allSelectors.indices) yield {
              if (i == updatedSelectorIndex)
                rhs.toTerm
              else
                allSelectors(i)._1(oldStructObjectTerm)
            }

            val newStructTerm = constructor(constructorArgs: _*)
            val wrapper = context.sortWrapperMap.getOrElse(structType.toSort,
                                                           throw new TranslationException(s"No heap wrapper for struct ${structType.shortName}"))
            val newHeapObject = CCTerm(wrapper(newStructTerm), CCHeapObject(context.heap), rhs.srcInfo)

            FunctionCall(
              functionName = writeFnName,
              args = Seq(rootPointer, newHeapObject),
              resultType = CCVoid,
              sourceInfo = rhs.srcInfo)

          case primitiveType =>
            // `lhs` is the term for the old value, e.g., `getInt(...)`.
            // `rhs` is the term for the new value, e.g., `42`.

            val wrapper = context.sortWrapperMap.getOrElse(primitiveType.toSort,
              throw new TranslationException(s"No heap wrapper for primitive type ${primitiveType}"))

            val newHeapObject = CCTerm(wrapper(rhs.toTerm), CCHeapObject(context.heap), rhs.srcInfo)

            FunctionCall(
              functionName = writeFnName,
              args = Seq(rootPointer, newHeapObject),
              resultType = CCVoid,
              sourceInfo = rhs.srcInfo
              )
        }

      case _ =>
        throw new TranslationException(
          "Field write attempted with a non-invariant-model pointer type.")
    }
  }

  override def getExitAssertions(exitPreds : Seq[CCPredicate]) = Seq()

  // ACSL stuff, these should be refactored to not require a heap term
  override def getACSLPreStateHeapTerm(
    acslContext : ACSLTranslator.FunctionContext) : ITerm = ???
  override def getACSLPostStateHeapTerm(
    acslContext : ACSLTranslator.FunctionContext) : ITerm = ???

  override def batchAlloc(o : CCTerm,
                          size : ITerm,
                          loc : ArrayLocation.Value,
                          s : Seq[CCExpr]) : HeapOperationResult = {
    ???
  }

  override def arrayRead(arr : CCExpr,
                         index : CCExpr,
                         s : Seq[CCExpr]) : HeapOperationResult = {
    ???
  }

  override def allocAndInitArray(arrayPtr         : CCHeapArrayPointer,
                                 size             : ITerm,
                                 initializers     : mutable.Stack[ITerm],
                                 s : Seq[CCExpr]) : HeapOperationResult = {
    ???
  }

  override def declUninitializedArray(arrayTyp         : CCHeapArrayPointer,
                                      size             : Option[ITerm],
                                      isGlobalOrStatic : Boolean,
                                      s : Seq[CCExpr]) : HeapOperationResult = {
    ???
  }
}
