/**
 * Copyright (c) 2015-2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.{ADT, ExtArray, Heap, ModuloArithmetic, Theory, TheoryRegistry}
import ap.types.{MonoSortedIFunction, MonoSortedPredicate, SortedConstantTerm}
import concurrent_c.{Absyn, _}
import concurrent_c.Absyn._
import hornconcurrency.ParametricEncoder
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintInitPred, VerifHintTplElement, VerifHintTplEqTerm, VerifHintTplPred}
import lazabs.horn.bottomup.HornClauses
import IExpression.{ConstantTerm, Predicate, Sort, toFunApplier}
import ap.theories.ADT.BoolADT
import lazabs.horn.extendedquantifiers.ExtendedQuantifier

import scala.collection.mutable.{ArrayBuffer, Buffer, Stack, HashMap => MHashMap, HashSet => MHashSet}
import tricera.Util._
import tricera.acsl.{ACSLTranslator, FunctionContract}
import tricera.params.TriCeraParameters
import tricera.parsers.AnnotationParser
import tricera.parsers.AnnotationParser._

object CCReader {
  def apply(input : java.io.Reader, entryFunction : String,
            arithMode : ArithmeticMode.Value = ArithmeticMode.Mathematical,
            trackMemorySafety : Boolean = false)
           : (CCReader, Boolean) = { // second ret. arg is true if modelled heap
    def entry(parser : concurrent_c.parser) = parser.pProgram
    val prog = parseWithEntry(input, entry _)
//    println(printer print prog)

    var useTime = false
    var modelHeap = false
    var reader : CCReader = null
    while (reader == null)
      try {
        reader = new CCReader(prog, entryFunction, useTime, modelHeap,
                              trackMemorySafety, arithMode)
      } catch {
        case NeedsTimeException => {
          warn("enabling time")
          useTime = true
        }
        case NeedsHeapModelException => {
          warn("enabling heap model")
          modelHeap = true
        }
      }
    (reader, modelHeap)
  }

  /**
   * Parse starting at an arbitrarily specified entry point
   */
  private[concurrency] def parseWithEntry[T](input : java.io.Reader,
                                             entry : (parser) => T) : T = {
    val l = new Yylex(new ap.parser.Parser2InputAbsy.CRRemover2 (input))
    val p = new parser(l, l.getSymbolFactory())

    try { entry(p) } catch {
      case e : Exception =>
        throw new ParseException(
             "At line " + String.valueOf(l.line_num()) +
             ", near \"" + l.buff() + "\" :" +
             "     " + e.getMessage())
    } finally {
      input.close
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  class ParseException(msg : String) extends Exception(msg)
  class TranslationException(msg : String) extends Exception(msg)
  class ExtendedQuantifierException(msg : String) extends Exception(msg)
  object NeedsTimeException extends Exception

  val heapTermName = "@h"
  object NeedsHeapModelException extends Exception

  object ArithmeticMode extends Enumeration {
    val Mathematical, ILP32, LP64, LLP64 = Value
  }

  //////////////////////////////////////////////////////////////////////////////

  // todo: maybe make private to package?
  abstract sealed class CCType (arithmeticMode : ArithmeticMode.Value) {
    def shortName : String

    import ModuloArithmetic._

    // todo: make this abstract. nice to have them all in the same place but would lead to runtime errors if there are missing cases.
    def toSort : Sort = arithmeticMode match {
      case ArithmeticMode.Mathematical => this match {
        case typ : CCArithType if typ.isUnsigned => Sort.Nat
        case CCDuration() => Sort.Nat
        case CCHeap(heap) => heap.HeapSort
        case CCStackPointer(_, _, _) => Sort.Integer
        case CCHeapPointer(heap, _) => heap.AddressSort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCArray(_, _, _, s, _) => s.sort
        case CCStruct(ctor, _) => ctor.resSort
        case CCStructField(n, s) => s(n).ctor.resSort
        case CCIntEnum(_, _) => Sort.Integer
        case _ => Sort.Integer
      }
      case ArithmeticMode.ILP32 => this match {
        case CCInt() => SignedBVSort(32)
        case CCUInt() => UnsignedBVSort(32)
        case CCLong() => SignedBVSort(32)
        case CCULong() => UnsignedBVSort(32)
        case CCLongLong() => SignedBVSort(64)
        case CCULongLong() => UnsignedBVSort(64)
        case CCDuration() => Sort.Nat
        case CCHeap(heap) => heap.HeapSort
        case CCStackPointer(_, _, _) => Sort.Integer
        case CCHeapPointer(heap, _) => heap.AddressSort
        case CCArray(_, _, _, s, _) => s.sort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCStruct(ctor, _) => ctor.resSort
        case CCStructField(n, s) => s(n).ctor.resSort
        case CCIntEnum(_, _) => Sort.Integer
        case _ => Sort.Integer
      }
      case ArithmeticMode.LP64 => this match {
        case CCInt() => SignedBVSort(32)
        case CCUInt() => UnsignedBVSort(32)
        case CCLong() => SignedBVSort(64)
        case CCULong() => UnsignedBVSort(64)
        case CCLongLong() => SignedBVSort(64)
        case CCULongLong() => UnsignedBVSort(64)
        case CCDuration() => Sort.Nat
        case CCHeap(heap) => heap.HeapSort
        case CCStackPointer(_, _, _) => Sort.Integer
        case CCHeapPointer(heap, _) => heap.AddressSort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCArray(_, _, _, s, _) => s.sort
        case CCStruct(ctor, _) => ctor.resSort
        case CCStructField(n, s) => s(n).ctor.resSort
        case CCIntEnum(_, _) => Sort.Integer
        case _ => Sort.Integer
      }
      case ArithmeticMode.LLP64 => this match {
        case CCInt() => SignedBVSort(32)
        case CCUInt() => UnsignedBVSort(32)
        case CCLong() => SignedBVSort(32)
        case CCULong() => UnsignedBVSort(32)
        case CCLongLong() => SignedBVSort(64)
        case CCULongLong() => UnsignedBVSort(64)
        case CCDuration() => Sort.Nat
        case CCHeap(heap) => heap.HeapSort
        case CCStackPointer(_, _, _) => Sort.Integer
        case CCHeapPointer(heap, _) => heap.AddressSort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCArray(_, _, _, s, _) => s.sort
        case CCStruct(ctor, _) => ctor.resSort
        case CCStructField(n, s) => s(n).ctor.resSort
        case CCIntEnum(_, _) => Sort.Integer
        case _ => Sort.Integer
      }
    }

    def rangePred(t : ITerm) : IFormula =
      toSort match {
        case Sort.Nat =>
          t >= 0
        case ModSort(lower, upper) =>
          t >= lower & t <= upper
        case _ => true // includes Integer, HeapAddress, ADTs
      }

    def range : (Option[IdealInt], Option[IdealInt]) = {
      toSort match {
        case Sort.Nat => (Some(IdealInt(0)), None)
        case Sort.Integer => (None, None)
        case ModSort(lower, upper) =>
          (Some(lower), Some(upper))
        case otherSort =>
          throw new TranslationException("Do not know how to get range for " +
            " sort " + otherSort)
      }
    }

    def newConstant(name : String) : ConstantTerm = toSort newConstant name

    def cast(t : ITerm) : ITerm = toSort match {
      case s : ModSort => cast2Sort(s, t)
      case _ => t
    }

    def cast2Unsigned(t : ITerm) : ITerm = toSort match {
      case SignedBVSort(n) => cast2UnsignedBV(n, t)
      case _ => t
    }

    def cast(e : CCExpr) : CCExpr = e match {
      case CCTerm(t, _, srcInfo)    => CCTerm(cast(t), this, srcInfo)
      case CCFormula(f, _, srcInfo) => CCFormula(f, this, srcInfo)
    }

    def getNonDet : ITerm =
      new SortedConstantTerm("_", toSort)

    // todo: make this abstract
    def getZeroInit : ITerm = this match {
      case structType : CCStruct =>
        import IExpression._
        val const: IndexedSeq[ITerm] =
          for ((_, fieldType) <- structType.sels) yield
            fieldType match {
              case CCStructField(name, structs) => structs(name).getZeroInit
              case _ => fieldType.getZeroInit
            }
        structType.ctor(const: _*)
      case CCHeapPointer(heap, _) => heap.nullAddr()
      case CCHeapArrayPointer(heap, _, _) => // todo: start = null, but size 0 or 1?
        heap.addressRangeCtor(heap.nullAddr(), IIntLit(1))
      case CCArray(_, _, _, arrayTheory, _) => arrayTheory.const(0)
      case _ => IIntLit(0)
    }
  }

  abstract class CCArithType(arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    val UNSIGNED_RANGE : IdealInt
    val isUnsigned : Boolean
  }
  case class CCVoid()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    override def toString : String = "void"
    def shortName = "void"
  }
  case class CCInt()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCArithType(arithmeticMode) {
    override def toString : String = "int"
    def shortName = "int"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFF", 16) // 32bit
    val isUnsigned : Boolean = false
  }
  case class CCUInt()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCArithType(arithmeticMode) {
    override def toString : String = "unsigned int"
    def shortName = "uint"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFF", 16) // 32bit
    val isUnsigned : Boolean = true
  }
  case class CCLong()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCArithType(arithmeticMode) {
    override def toString : String = "long"
    def shortName = "long"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = false
  }
  case class CCULong()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCArithType(arithmeticMode) {
    override def toString : String = "unsigned long"
    def shortName = "ulong"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = true
  }
  case class CCLongLong()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCArithType(arithmeticMode) {
    override def toString : String = "long long"
    def shortName = "llong"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = false
  }
  case class CCULongLong()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCArithType(arithmeticMode) {
    override def toString : String = "unsigned long long"
    def shortName = "ullong"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = true
  }

  case class CCHeap(heap : Heap)
                   (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    override def toString : String = heap.toString
    def shortName = "heap"
  }

  /**
   * typ is either an index into structInfos (if ADT type), or a CCType
   * ptrDepth 0 => not a pointer, 1 => *, 2 => **, ...*/
  case class FieldInfo(name : String,
                               typ : Either[Integer, CCType],
                               ptrDepth : Integer)
  case class StructInfo(name : String, fieldInfos : Seq[FieldInfo])

  case class CCStructField(structName : String,
                           structs    : MHashMap[String, CCStruct])
                          (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode){
    override def toString : String = "field with type: " + structName
    def shortName = "field:" + structName
  }
  case class CCStruct(ctor : MonoSortedIFunction,
                      sels : IndexedSeq[(MonoSortedIFunction, CCType)])
                     (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode){
    override def toString : String =
      "struct " + ctor.name + ": (" +sels.mkString + ")"
    def shortName = ctor.name
    def getFieldIndex(name: String) =  sels.indexWhere(_._1.name == name)
    def getFieldAddress (nestedName: List[String]) : List[Int] =
      nestedName match{
        case hd::Nil => getFieldIndex(hd) :: Nil
        case hd::tl => {
          val ind = getFieldIndex(hd)
          val typ = getFieldType(ind).asInstanceOf[CCStruct]
          ind :: typ.getFieldAddress(tl)
        }
        case Nil => Nil // not possible to reach
      }
    def getFieldType(ind: Int) : CCType = sels(ind)._2 match {
      case CCStructField(name, structs) => structs(name)
      case typ => typ
    }
    def getFieldType(fieldAddress: List[Int]) : CCType =
      fieldAddress match{
        case hd::Nil => getFieldType(hd)
        case hd::tl => getFieldType(hd).asInstanceOf[CCStruct].getFieldType(tl)
        case Nil => throw new TranslationException("Field type requested with" +
          "empty field index!")
      }

    def contains(fieldName: String) = getFieldIndex(fieldName) != -1
    def getFieldTerm(t: ITerm, fieldAddress: List[Int]) : ITerm = {
      val hd :: tl = fieldAddress
      val sel = getADTSelector(hd)
      getFieldType(hd) match {
        case nested : CCStructField =>
          tl match {
            case Nil => sel(t)
            case _ => nested.structs(nested.structName).getFieldTerm (sel(t), tl)
          }
        case nested : CCStruct => // todo: simplify
          tl match {
            case Nil => sel(t)
            case _ => nested.getFieldTerm (sel(t), tl)
          }
        case _ => sel(t)
      }
    }
    def setFieldTerm(rootTerm: ITerm, setVal: ITerm,
                     fieldAddress: List[Int]) : ITerm = {
      fieldAddress match {
        case hd :: tl => {
          val childTerm = getFieldType(hd) match {
            case nx : CCStruct if tl != Nil =>
              nx.setFieldTerm(getADTSelector(hd)(rootTerm), setVal, tl)
            case nx : CCStructField if tl != Nil =>
              nx.structs(nx.structName).setFieldTerm(
                getADTSelector(hd)(rootTerm), setVal, tl)
            //case nx: CCStruct if tl!= Nil =>
            //    nx.setFieldTerm(getADTSelector(hd)(rootTerm), setVal, tl)
            case _ => setVal
          }
          val const =
            for (n <- sels.indices) yield {
              if (n == hd) childTerm
              else getADTSelector(n)(rootTerm)
            }
          ctor(const: _*).asInstanceOf[ITerm]
        }
        case Nil => throw new TranslationException("setFieldTerm called with" +
          " empty List!")
      }
    }

    def getADTSelector(ind: Int) : MonoSortedIFunction = sels(ind)._1

    // Initializes a struct using a stack and returns the initialized term.
    // The stack's top value must be the first term of the struct.
    // The fields are initialized left to right depth-first.
    // If there are not enough values to initialize all the fields, then the
    // remaining fields are initialized to 0.
    def getInitialized(values: Stack[ITerm]): ITerm = {
      import IExpression._
      val const: IndexedSeq[ITerm] =
        for (field <- sels) yield
          field._2 match {
            case CCStructField(name,structs) =>
              structs(name).getInitialized(values)
            case s : CCStruct => s.getInitialized(values)
            case CCHeapPointer(h, _) =>
              if (values.isEmpty) h.nullAddr() else values.pop()
            case CCHeapArrayPointer(h, _, _) =>
              throw new TranslationException("Heap arrays inside structs are" +
                "not supported.")
              ???
              if (values.isEmpty)
                h.addressRangeCtor(h.nullAddr(), IIntLit(1))
              else values.pop()
            case CCArray(elemTyp, sizeExpr, Some(arraySize), arrayTheory, arrayLocation) => // todo: use arrLoc?
              val initialArrayTerm = new SortedConstantTerm(field._1.name, arrayTheory.objSort)
              def arrayBatchStore(arr : ITerm, ind : Int, n : Int) : ITerm = {
                if(ind >= n)
                  arr else {
                  val innerArr = arrayTheory.store(arr, Int2ITerm(ind),
                    if (values.isEmpty) {
                      if (elemTyp.isInstanceOf[CCArithType]) {
                        IIntLit(0)
                        // todo: use actual sorts! need rich types here
                      } else {
                        throw new TranslationException("")
                        // todo: this can be supported if we have access to
                        //   rich types here
                      }
                    }
                    else values.pop())
                  arrayBatchStore(innerArr, ind + 1, n)
                }
              }
              arrayBatchStore(initialArrayTerm, 0, arraySize)
            case _ => if (values.isEmpty) Int2ITerm(0) else values.pop()
          }
      ctor(const: _*)
    }
  }

  /**
   * Type for enums that are directly mapped to integers
   */
  case class CCIntEnum(name: String,
                       enumerators: Seq[(String, IdealInt)])
                      (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode){
    override def toString : String =
      "enum-int " + name + ": (" + enumerators.mkString + ")"
    def shortName = name
  }

  abstract sealed class CCPointer(typ : CCType)
                                 (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    def shortName = typ.shortName + "*"
  }
  case class CCStackPointer(targetInd    : Int, typ : CCType,
                            fieldAddress : List[Int] = Nil)
                           (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCPointer(typ) {
    override def toString : String = typ.shortName +
      " pointer (to: " + targetInd + ")"

  }

  // todo: how to support heap pointers to adt fields? should we?
  // e.g.: what does &(p->x) return when p is a heap pointer?
  //       needs to be a Heap.Address along with a way to reach the field
  //       maybe another class for this? CCHeapADTFieldPointer...
  case class CCHeapPointer(heap : Heap,
                           typ : CCType)
                          (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCPointer(typ) {
    override def toString : String = typ.shortName + " pointer to heap"
  }

  // arrays on the heap do not get automatically freed.
  // global arrays get automatically freed (as they are not really on the heap)
  //   when the main function returns.
  // "alloca" and stack arrays get automatically freed when the calling function returns.
  object ArrayLocation extends Enumeration {
    type ArrayLocation = Value
    val GlobalArray, StackArray, HeapArray = Value
  }
  import ArrayLocation._
  case class CCHeapArrayPointer(heap : Heap,
                                elementType   : CCType,
                                arrayLocation : ArrayLocation)
                               (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    def shortName = "[]"
  }


  // uses the theory of arrays (and not heaps). this is used for InitArray's
  // which appear as struct fields (e.g. struct S{int a[4];})
  // and for mathematical arrays (then sizeExpr and sizeInt can be None).
  case class CCArray(elementType : CCType, // todo: multidimensional arrays?
                     sizeExpr    : Option[CCExpr],
                     sizeInt     : Option[Int],
                     arrayTheory : ap.theories.ExtArray,
                     arrayLocation : ArrayLocation)
                    (implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    override def toString : String =
      //typ + "[" + (if (size.nonEmpty) size.get else "") + "]"
      elementType + " array"
    def shortName = elementType + "[]"
  }

  case class CCClock()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    override def toString : String = "clock"
    def shortName = "clock"
  }
  case class CCDuration()(implicit arithmeticMode : ArithmeticMode.Value)
    extends CCType(arithmeticMode) {
    override def toString : String = "duration"
    def shortName = "duration"
  }
  //////////////////////////////////////////////////////////////////////////////

  abstract sealed class CCExpr(val typ : CCType,
                               val srcInfo : Option[SourceInfo]) {
    def toTerm : ITerm
    def toFormula : IFormula
    def occurringConstants : Seq[IExpression.ConstantTerm]
  }
  case class CCTerm(t : ITerm, _typ : CCType, _srcInfo : Option[SourceInfo])
               extends CCExpr(_typ, _srcInfo) {
    def toTerm : ITerm = t
    def toFormula : IFormula = t match {
      case IIntLit(value) => !value.isZero
      case t if _typ.isInstanceOf[CCHeapPointer] => !IExpression.Eq(t,
        _typ.asInstanceOf[CCHeapPointer].heap.nullAddr())
      case t =>              !IExpression.eqZero(t)
    }
    def occurringConstants : Seq[IExpression.ConstantTerm] =
      SymbolCollector constantsSorted t
  }
  case class CCFormula(f : IFormula, _typ : CCType,
                       _srcInfo : Option[SourceInfo])
                     extends CCExpr(_typ, _srcInfo : Option[SourceInfo]) {
    def toTerm : ITerm = f match {
      case IBoolLit(true) =>  1
      case IBoolLit(false) => 0
      case f =>               IExpression.ite(f, 1, 0)
    }
    def toFormula : IFormula = f
    def occurringConstants : Seq[IExpression.ConstantTerm] =
      SymbolCollector constantsSorted f
  }

  object CCVar{
    val lineNumberPrefix  = ":"
  }
  class CCVar (val name : String,
               val srcInfo : Option[SourceInfo],
               val typ  : CCType) {
    import CCVar._
    val nameWithLineNumber = name +
      (srcInfo match {
        case Some(info) if info.line >= 0 => lineNumberPrefix + info.line
        case _ => ""
      } )
    val sort = typ.toSort
    val term = {
      val termName =
      if (TriCeraParameters.get.showVarLineNumbersInTerms)
        nameWithLineNumber else name
      new SortedConstantTerm(termName, sort)
    }
    def rangePred : IFormula = typ rangePred term
    override def toString: String =
      if (TriCeraParameters.get.showVarLineNumbersInTerms)
        nameWithLineNumber else name
    def toStringWithLineNumbers: String = name + {
      srcInfo match {
        case Some(info) if info.line >= 0 => lineNumberPrefix + info.line
        case _ => ""
      }
    }
  }

  case class CCClause (clause : HornClauses.Clause,
                       srcInfo : Option[SourceInfo]) // todo: what else would be useful?

  // a wrapper for IExpression.Predicate that keeps more info about arguments
  case class CCPredicate(pred : Predicate, argVars : Seq[CCVar],
                         srcInfo : Option[SourceInfo]) {
    import ap.parser.ITerm
    import IExpression._
    def apply(terms : Seq[ITerm]) = pred(terms: _*)
    def apply[X: scala.reflect.ClassTag](ccVars : Seq[CCVar]) =
      pred(ccVars.map(_.term): _*)
    def arity : Int = pred.arity
    override def toString: String =
      pred.name + (if(argVars.nonEmpty) "(" + argVars.mkString(", ") + ")" else "")
    def toStringWithLineNumbers: String =
      pred.name + (if(argVars.nonEmpty) "(" +
        argVars.map(_.toStringWithLineNumbers).mkString(", ") + ")" else "")
    assert(pred.arity == argVars.size)
  }

  class FunctionContext (val prePred  : CCPredicate,
                         val postPred : CCPredicate,
                         val acslContext : ACSLTranslator.FunctionContext,
                         val prePredACSLArgNames : Seq[String],
                         val postPredACSLArgNames : Seq[String])

}

////////////////////////////////////////////////////////////////////////////////

class CCReader private (prog : Program,
                        entryFunction : String,
                        useTime : Boolean,
                        modelHeap : Boolean,
                        trackMemorySafety : Boolean,
                        arithmeticMode : CCReader.ArithmeticMode.Value) {

  import CCReader._
  import CCReader.ArrayLocation._

  private val printer = new PrettyPrinterNonStatic

  implicit val _arithmeticMode = arithmeticMode

  //////////////////////////////////////////////////////////////////////////////

  private implicit def toRichExpr(expr : CCExpr) :
    Object{def mapTerm(m:ITerm => ITerm) : CCExpr} = new Object {
    def mapTerm(m : ITerm => ITerm) : CCExpr =
    // TODO: type promotion when needed
    CCTerm(expr.typ cast m(expr.toTerm), expr.typ, expr.srcInfo)
  }

  //////////////////////////////////////////////////////////////////////////////

  import HornClauses.Clause

  private val predCCPredMap = new MHashMap[Predicate, CCPredicate]

  private sealed class CCVars {
    val vars = new ArrayBuffer[CCVar]
    def addVar (v : CCVar) : Int = {
      vars += v
      size - 1
    }
    def size : Int = vars.size
    def lastIndexWhere(name : String) = vars lastIndexWhere(_.name == name)
    def contains (c : ConstantTerm) = vars exists (_.term == c)
    def iterator = vars.iterator
    def formalVars = vars.toList
    def formalVarTerms = vars.map(_.term).toList
    def formalTypes = vars.map(_.typ).toList
  }

  private object globalVars extends CCVars {
    val inits = new ArrayBuffer[CCExpr]
  }
  private object localVars extends CCVars {
    val frameStack = new Stack[Int]

    override def addVar (v : CCVar) : Int = {
      variableHints += List()
      super.addVar(v)
    }
    def pop(n : Int) = {
      localVars trimEnd n
      variableHints trimEnd n
      assert(variableHints.size == size + globalVars.size)
    }

    def remove(n : Int): Unit = {
      assume(n >= 0 && n < size)
      vars.remove(n)
      variableHints.remove(n + globalVars.size)
    }
    def trimEnd(n: Int) = vars trimEnd n
    def pushFrame = frameStack push size
    def popFrame = {
      val newSize = frameStack.pop
      vars reduceToSize newSize
      variableHints reduceToSize (globalVars.size + newSize)
    }
    def getVarsInTopFrame : List[CCVar] =
      (vars takeRight (vars.size - frameStack.last)).toList
  }

  private def updateVarType(name : String, newType : CCType) = {
    val ind = lookupVar(name)
    if (ind < globalVars.size) {
      val oldVar = globalVars.vars(ind)
      globalVars.vars(ind) =
        new CCVar(name, oldVar.srcInfo, newType)
    } else {
      val oldVar = localVars.vars(ind - globalVars.size)
      localVars.vars(ind - globalVars.size) =
        new CCVar(name, oldVar.srcInfo, newType)
    }
  }

  private var globalPreconditions : IFormula = true
  private val globalExitPred = newPred("exit", Nil, None)

  private def lookupVarNoException(name : String) : Int =
    localVars lastIndexWhere name match {
      case -1 => globalVars lastIndexWhere name
      case i  => i + globalVars.size
    }

  private def lookupVar(name : String) : Int = {
    val actualName =
      if (TriCeraParameters.get.showVarLineNumbersInTerms) {
        name.lastIndexOf(CCVar.lineNumberPrefix) match {
            case -1 => name
            case i => name.take(i)
          }
      } else name
    lookupVarNoException(actualName) match {
      case -1 =>
        actualName match {
          case `heapTermName` if !modelHeap => throw NeedsHeapModelException
          case _ => throw new TranslationException(
            "Symbol " + actualName + " is not declared")
        }
      case i => i
    }
  }

  private def allFormalVars : Seq[CCVar] =
    globalVars.formalVars ++ localVars.formalVars
  private def allFormalVarTerms : Seq[ITerm] =
    globalVars.formalVarTerms ++ localVars.formalVarTerms
  private def allFormalVarTypes : Seq[CCType] =
    globalVars.formalTypes ++ localVars.formalTypes

  private def allFormalExprs : Seq[CCExpr] =
    ((for (v <- globalVars.iterator)
      yield CCTerm(v.term, v.typ, v.srcInfo)) ++
     (for (v <- localVars.iterator)
      yield CCTerm(v.term, v.typ, v.srcInfo))).toList
  private def allVarInits : Seq[ITerm] =
    (globalVars.inits.toList map (_.toTerm)) ++
      (localVars.formalVarTerms map (IExpression.i(_)))

  private def freeFromGlobal(t : IExpression) : Boolean =
    !ContainsSymbol(t, (s:IExpression) => s match {
                      case IConstant(c) => globalVars contains c
                      case _ => false
                    })

  private def freeFromGlobal(t : CCExpr) : Boolean = t match {
    case CCTerm(s, _, _) =>    freeFromGlobal(s)
    case CCFormula(f, _, _) => freeFromGlobal(f)
  }

  private val variableHints =
    new ArrayBuffer[Seq[VerifHintElement]]
  private var usingInitialPredicates = false

  //////////////////////////////////////////////////////////////////////////////

  private var tempVarCounter = 0

  private def getFreshEvalVar (typ : CCType) : CCVar = {
    val res = new CCVar("__eval" + tempVarCounter, None, typ) // todo: src/line no info?
    tempVarCounter = tempVarCounter + 1
    res
  }


  //////////////////////////////////////////////////////////////////////////////

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  private val functionDefs  = new MHashMap[String, Function_def]
  private val functionExitPreds = new MHashMap[String, CCPredicate]
  private val functionDecls = new MHashMap[String, (Direct_declarator, CCType)]
  private val functionContexts = new MHashMap[String, FunctionContext]
  private val functionPostOldArgs = new MHashMap[String, Seq[CCVar]]
  private val functionClauses =
    new MHashMap[String, Seq[(Clause, ParametricEncoder.Synchronisation)]]
  private val functionAssertionClauses = new MHashMap[String, Seq[CCClause]]
  private val uniqueStructs = new MHashMap[Unique, String]
  private val structInfos   = new ArrayBuffer[StructInfo]
  private val structDefs    = new MHashMap[String, CCStruct]
  private val enumDefs      = new MHashMap[String, CCType]
  private val enumeratorDefs= new MHashMap[String, CCExpr]

  private val uninterpPredDecls     = new MHashMap[String, CCPredicate]
  private val loopInvariants        =
    new MHashMap[String, (CCPredicate, SourceInfo)]

  def getLoopInvariants = loopInvariants.toMap
  def getFunctionContexts = functionContexts.toMap

  // NOTE: Used by ACSL encoder.
  var hasACSLEntryFunction : Boolean = false
  val funToPreAtom  : MHashMap[String, IAtom] = new MHashMap()
  val funToPostAtom : MHashMap[String, IAtom] = new MHashMap()
  val funToContract : MHashMap[String, FunctionContract] = new MHashMap()
  val funsWithAnnot : MHashSet[String] = new MHashSet()
  val prePredsToReplace : MHashSet[Predicate] = new MHashSet()
  val postPredsToReplace : MHashSet[Predicate] = new MHashSet()

  //////////////////////////////////////////////////////////////////////////////

  private val processes =
    new ArrayBuffer[(ParametricEncoder.Process, ParametricEncoder.Replication)]

  private val assertionClauses = new ArrayBuffer[CCClause]
  private val timeInvariants = new ArrayBuffer[Clause]

  private val clauses =
    new ArrayBuffer[(Clause, ParametricEncoder.Synchronisation)]

  private def output(c : Clause,
                     sync : ParametricEncoder.Synchronisation =
                       ParametricEncoder.NoSync) : Unit = {
    clauses += ((c, sync))
  }

  import ParametricEncoder.merge

  private def mergeClauses(from : Int) : Unit = if (from < clauses.size - 1) {
    val concernedClauses = clauses.slice(from, clauses.size)
    val (entryClauses, transitionClauses) =
      if (concernedClauses.head._1.body.isEmpty) {
        concernedClauses partition (_._1.body.isEmpty)
      } else {
        val entryPred = concernedClauses.head._1.body.head.pred
        concernedClauses partition (_._1.body.head.pred == entryPred)
      }
    val lastClauses = transitionClauses groupBy (_._1.body.head.pred)

    clauses reduceToSize from

    def chainClauses(currentClause : Clause,
                     currentSync : ParametricEncoder.Synchronisation,
                     seenPreds : Set[Predicate]) : Unit =
      if (!currentClause.hasUnsatConstraint) {
        val headPred = currentClause.head.pred
        if (seenPreds contains headPred)
          throw new TranslationException(
            "cycles in atomic blocks are not supported yet")

        (lastClauses get headPred) match {
          case Some(cls) => {
            if (timeInvariants exists (_.predicates contains headPred))
              throw new TranslationException(
                "time invariants in atomic blocks are not supported")

            for ((c, sync) <- cls)
              if (currentSync == ParametricEncoder.NoSync)
                chainClauses(merge(c, currentClause), sync,
                             seenPreds + headPred)
              else if (sync == ParametricEncoder.NoSync)
                chainClauses(merge(c, currentClause), currentSync,
                             seenPreds + headPred)
              else
                throw new TranslationException(
                  "Cannot execute " + currentSync + " and " + sync +
                  " in one step")

            // add further assertion clauses, since some intermediate
            // states disappear
            for (c <- assertionClauses.toList)
              if (c.clause.bodyPredicates contains headPred) {
                if (currentSync != ParametricEncoder.NoSync)
                  throw new TranslationException(
                    "Cannot execute " + currentSync + " and an assertion" +
                    " in one step")
                val newAssertionClause = merge(c.clause, currentClause)
                if (!newAssertionClause.hasUnsatConstraint)
                  assertionClauses += CCClause(newAssertionClause, c.srcInfo)
              }
          }
          case None =>
            clauses += ((currentClause, currentSync))
        }
      }

    for ((c, sync) <- entryClauses)
      chainClauses(c, sync, Set())
  }

  private var atomicMode = false

  private def inAtomicMode[A](comp : => A) : A = {
      val oldAtomicMode = atomicMode
      atomicMode = true
      val res = comp
      atomicMode = oldAtomicMode
      res
  }

  private var noSideEffects = false

  private def withoutSideEffects[A](comp : => A) : A = {
    val oldNoSideEffects = noSideEffects
    noSideEffects = true
    val res = comp
    noSideEffects = oldNoSideEffects
    res
  }

  private var prefix : String = ""
  private var locationCounter = 0

  private def setPrefix(pref : String) = {
    prefix = pref
    locationCounter = 0
  }

  def addLoopInvariant(pred : CCPredicate, srcInfo : SourceInfo) : Unit = {
    loopInvariants += ((pred.pred.name, (pred, srcInfo)))
  }

  def newPred(name : String,
              args : Seq[CCVar],
              srcInfo : Option[SourceInfo]) : CCPredicate = {
    val pred = MonoSortedPredicate(name, args map (_ sort))
    val ccPred = CCPredicate(pred, args, srcInfo)
    predCCPredMap.put(pred, ccPred)
    ccPred
  }

  private def newPred(extraArgs : Seq[CCVar],
                      srcInfo : Option[SourceInfo]) : CCPredicate = {
    val res = newPred(prefix + locationCounter, allFormalVars ++ extraArgs, srcInfo)
    locationCounter = locationCounter + 1

    val hints = for (s <- variableHints; p <- s) yield p
    val allHints =
      if (hints exists (_.isInstanceOf[VerifHintTplElement])) {
        // make sure that all individual variables exist as templates
        val coveredVars =
          (for (VerifHintTplEqTerm(IVariable(n), _) <- hints.iterator)
           yield n).toSet
        hints ++ (for (n <- (0 until res.arity).iterator;
                       if (!(coveredVars contains n)))
                  yield VerifHintTplEqTerm(IExpression.v(n), 10000))
      } else {
        hints
      }

    predicateHints.put(res.pred, allHints)
    res
  }

  private val predicateHints =
    new MHashMap[Predicate, Seq[VerifHintElement]]

  //////////////////////////////////////////////////////////////////////////////

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  // Reserve two variables for time
  private val GT = new CCVar("_GT", None, CCClock())
  private val GTU = new CCVar("_GTU", None, CCInt())

  if (useTime) {
    globalVars addVar GT
    globalVars.inits += CCTerm(GT.term, CCClock(), None)
    globalVars addVar GTU
    globalVars.inits += CCTerm(GTU.term, CCInt(), None)
    variableHints += List()
    variableHints += List()
  }

  private def collectStructDefsFromComp (comp : Compound_stm): Unit = {
    comp match {
      case        _: ScompOne =>
      case compound: ScompTwo =>
        val stmsIt = ap.util.PeekIterator(compound.liststm_.iterator)
        while (stmsIt.hasNext) stmsIt.next match {
          case dec: DecS => collectStructDefs(dec.dec_)
          case _ =>
        }
    }
  }

  implicit def annotationStringExtractor(annot : Annotation) : String = {
    val str = annot match {
      case a : Annot1 => a.annotationstring_
    }
    str.substring(2, str.length-2) // removes the annotation markers
  }

  object FuncDef {
    def apply(funDef : Function_def) : FuncDef = {
      funDef match {
        case f : NewFunc =>
          FuncDef(f.compound_stm_, f.declarator_,
                  getSourceInfo(f),
                  Some(f.listdeclaration_specifier_),
                  Nil)
        case f : NewFuncInt =>
          FuncDef(f.compound_stm_, f.declarator_,
                  getSourceInfo(f), None,
                  f.listannotation_)
        case f : AnnotatedFunc =>
          FuncDef(f.compound_stm_, f.declarator_,
                  getSourceInfo(f),
                  Some(f.listdeclaration_specifier_),
                  f.listannotation_)
      }
    }
  }
  case class FuncDef(body : Compound_stm,
                     decl : Declarator,
                     sourceInfo : SourceInfo,
                     declSpecs : Option[ListDeclaration_specifier] = None,
                     annotations : Seq[Annotation]) {
    val name : String = getName(decl)
  }

  for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
    decl match {
      case decl: Global => collectStructDefs(decl.dec_)
      case fun: Afunc =>
        val comp = FuncDef(fun.function_def_).body
        collectStructDefsFromComp(comp)
      case thread : Athread =>
        val comp = thread.thread_def_ match {
          case t : SingleThread => t.compound_stm_
          case t : ParaThread => t.compound_stm_
        }
        collectStructDefsFromComp(comp)
      case _ =>
    }

  import ap.theories.{Heap => HeapObj}

  def defObjCtor(objectCtors : Seq[IFunction],
                 heapADTs : ADT) : ITerm = {
    objectCtors.last()
  }

  val ObjSort = HeapObj.ADTSort(0)

  val structCtorSignatures : List[(String, HeapObj.CtorSignature)] =
    (for (i <- structInfos.indices) yield {
      if(structInfos(i).fieldInfos isEmpty) warn(
        "Struct " + structInfos(i).name + " was declared, but never defined, " +
          "or it has no fields.")
      val ADTFieldList : Seq[(String, HeapObj.CtorArgSort)] =
        for(FieldInfo(fieldName, fieldType, ptrDepth) <-
              structInfos(i).fieldInfos) yield
          (fieldName,
            if (ptrDepth > 0) Heap.AddressCtor
            else { fieldType match {
              case Left(ind) => HeapObj.ADTSort(ind + 1)
              case Right(typ) =>
                typ match {
                  case _ : CCHeapArrayPointer => HeapObj.AddressRangeCtor
                  case _ => HeapObj.OtherSort(typ.toSort)
                }
            }
            })
      (structInfos(i).name, HeapObj.CtorSignature(ADTFieldList, HeapObj.ADTSort(i+1)))
    }).toList

  // todo: only add types that exist in the program - should also add machine arithmetic types
  val predefSignatures =
    List(("O_Int", HeapObj.CtorSignature(List(("getInt", HeapObj.OtherSort(Sort.Integer))), ObjSort)),
         ("O_UInt", HeapObj.CtorSignature(List(("getUInt", HeapObj.OtherSort(Sort.Nat))), ObjSort)),
         ("O_Addr", HeapObj.CtorSignature(List(("getAddr", HeapObj.AddressCtor)), ObjSort)),
         ("O_AddrRange", HeapObj.CtorSignature(List(("getAddrRange", HeapObj.AddressRangeCtor)), ObjSort))
    )

  val wrapperSignatures : List[(String, HeapObj.CtorSignature)] =
    predefSignatures ++
      (for ((name, signature) <- structCtorSignatures) yield {
        ("O_" + name,
          HeapObj.CtorSignature(List(("get" + name, signature.result)), ObjSort))
      })

  val heap = new Heap("Heap", "Addr", ObjSort,
    List("HeapObject") ++ structCtorSignatures.unzip._1,
    wrapperSignatures ++ structCtorSignatures ++
      List(("defObj", HeapObj.CtorSignature(List(), ObjSort))),
    defObjCtor)

  private val heapVar = new CCVar(heapTermName, None, CCHeap(heap))
  val heapTerm = heapVar.term

  if (modelHeap) {
    globalVars addVar heapVar

    globalVars.inits += CCTerm(heap.emptyHeap(), CCHeap(heap), None)
    variableHints += List()
  }

  private val structCtorsOffset = predefSignatures.size
  val defObj = heap.userADTCtors.last
  val structCount = structInfos.size
  val objectWrappers = heap.userADTCtors.take(structCount+structCtorsOffset)
  val objectGetters =
    for (sels <- heap.userADTSels.take(structCount+structCtorsOffset)
         if sels.nonEmpty) yield sels.head
  val structCtors = heap.userADTCtors.slice(structCtorsOffset+structCount,
    structCtorsOffset+2*structCount)
  val structSels = heap.userADTSels.slice(structCtorsOffset+structCount,
    structCtorsOffset+2*structCount)

  val objectSorts : IndexedSeq[Sort] = objectGetters.toIndexedSeq.map(f => f.resSort)
  val sortGetterMap : Map[Sort, MonoSortedIFunction] =
    objectSorts.zip(objectGetters).toMap
  val sortWrapperMap : Map[Sort, MonoSortedIFunction] =
    objectSorts.zip(objectWrappers).toMap
  val sortCtorIdMap : Map[Sort, Int] =
    objectSorts.zip(0 until structCount+structCtorsOffset).toMap

  for (((ctor, sels), i) <- structCtors zip structSels zipWithIndex) {
    val fieldInfos = structInfos(i).fieldInfos
    val fieldsWithType = for (j <- fieldInfos.indices) yield {
      assert(sels(j).name == fieldInfos(j).name)
      (sels(j),{
        val actualType = fieldInfos(j).typ match {
        case Left(ind) => CCStructField(structInfos(ind).name, structDefs)
        case Right(typ) =>
          typ match {
            case t : CCHeapArrayPointer => // replace with initialized heap
              CCHeapArrayPointer(heap, t.elementType, t.arrayLocation) // todo: would fail for arrays of arrays inside structs
            case _ => typ
          }
      }
      if(fieldInfos(j).ptrDepth > 0) CCHeapPointer(heap, actualType)
      else actualType})}
    structDefs += ((ctor.name, CCStruct(ctor, fieldsWithType)))
  }

  private var funRetCounter = 0
  private def getResVar (typ : CCType) : List[CCVar] = typ match {
    case _ : CCVoid => Nil
    case t          =>
      funRetCounter += 1
      List(new CCVar("_res" + funRetCounter, None, typ)) // todo: line no?
  }

  private def translateProgram : Unit = {
    // First collect all declarations. This is a bit more
    // generous than actual C semantics, where declarations
    // have to be in the right order
    import IExpression._
    atomicMode = true
    val globalVarSymex = Symex(null)

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Global =>
          collectVarDecls(decl.dec_, true, globalVarSymex)

        case decl : Chan =>
          for (name <- decl.chan_def_.asInstanceOf[AChan].listcident_) {
            if (channels contains name)
              throw new TranslationException(
                "Channel " + name + " is already declared")
            channels.put(name, new ParametricEncoder.CommChannel(name))
          }

        case decl : Afunc => {
          val name = getName(decl.function_def_)

          if (functionDefs contains name)
            throw new TranslationException(
              "Function " + name + " is already declared")
          functionDefs.put(name, decl.function_def_)
        }

        case _ =>
          // nothing
      }

    // prevent time variables and heap variable from being initialised twice
    globalVars.inits ++= (globalVarSymex.getValues drop
      (if (modelHeap) 1 else 0) + (if (useTime) 2 else 0))
    // if while adding glboal variables we have changed the heap, the heap term
    // needs to be reinitialised as well. Happens with global array allocations.
    if (modelHeap) {
      val initialisedHeapValue = globalVarSymex.getValues.head
      val initialHeapValue = IConstant(globalVars.vars.head.term)
      if (modelHeap && initialisedHeapValue.toTerm != initialHeapValue) {
        globalVars.inits(0) = initialisedHeapValue
      }
    }


    globalPreconditions = globalPreconditions &&& globalVarSymex.getGuard

    // todo: what about functions without definitions? replace Afunc type
    val functionAnnotations : Map[Afunc, Seq[AnnotationInfo]] =
      prog.asInstanceOf[Progr].listexternal_declaration_.collect {
        case f : Afunc  =>
          val annots = f.function_def_ match {
            case f: AnnotatedFunc => f.listannotation_.toList
            case f: NewFuncInt    => f.listannotation_.toList
            case _: NewFunc       => Nil
          }
          (f, (for (annot <- annots) yield
            AnnotationParser(annot)).flatten)
      }.toMap

    // functions for which contracts should be generated
    // todo: generate contracts for ACSL annotated funs
    val contractFuns : Seq[Afunc] =
      functionAnnotations.filter(_._2.exists(_ == ContractGen)).keys.toSeq

    val funsThatMightHaveACSLContracts : Map[Afunc, Seq[AnnotationInfo]] =
      functionAnnotations.filter(_._2.exists(_.isInstanceOf[MaybeACSLAnnotation]))

    for(fun <- contractFuns ++ funsThatMightHaveACSLContracts.keys) {
      val funDef = FuncDef(fun.function_def_)
      localVars.pushFrame
      pushArguments(fun.function_def_)
      val functionParams = localVars getVarsInTopFrame

      val oldVars = allFormalVars map (v =>
        new CCVar(v.name + "_old", v.srcInfo, v.typ))
      // the pre-condition: f_pre(preOldVars)
      val prePred = newPred(funDef.name + "_pre", oldVars,
        Some(getSourceInfo(fun)))

      // the post-condition: f_post(oldVars, postGlobalVars, postResVar)
      // we first pass all current vars in context as old vars (oldVars)
      // then we pass all effected output vars (which are globals + resVar)
      val postGlobalVars = globalVars.vars map (v =>
        new CCVar(v.name + "_post", v.srcInfo, v.typ))
      val postResVar = getType(fun.function_def_) match {
        case _: CCVoid => None
        case _ => Some(new CCVar(funDef.name + "_res",
          Some(funDef.sourceInfo), getType(fun.function_def_))) // todo: clean this (and similar code) up a bit
      }
      val postVars = oldVars ++ postGlobalVars ++ postResVar
      functionPostOldArgs.put(funDef.name, oldVars)

      val prePredArgACSLNames = allFormalVars map (_.name)
      val postPredACSLArgNames =
        allFormalVars.map(v => "\\old(" + v.name + ")") ++
        globalVars.vars.map(v => v.name) ++ Seq("\\result")

      val postOldVarsMap: Map[String, CCVar] =
      (allFormalVars.map(_ name) zip oldVars).toMap
      val postGlobalVarsMap: Map[String, CCVar] =
        (globalVars.vars.map(_ name) zip postGlobalVars).toMap

      val postPred = newPred(funDef.name + "_post", postVars,
        Some(getSourceInfo(fun))) // todo: end line of fun?

      localVars.popFrame

      class ReaderFunctionContext extends ACSLTranslator.FunctionContext {
        def getOldVar(ident: String): Option[CCVar] =
          postOldVarsMap get ident

        def getPostGlobalVar(ident: String): Option[CCVar] =
          postGlobalVarsMap get ident

        def getParams: Seq[CCReader.CCVar] = functionParams

        def getGlobals: Seq[CCReader.CCVar] = globalVars.vars - heapVar

        def getResultVar: Option[CCReader.CCVar] = postResVar

        def isHeapEnabled: Boolean = modelHeap

        def getHeap: Heap =
          if (modelHeap) heap else throw NeedsHeapModelException

        def getHeapTerm: ITerm =
          if (modelHeap) getPostGlobalVar(heapTermName).get.term
          else throw NeedsHeapModelException

        def getOldHeapTerm: ITerm =
          if (modelHeap) getOldVar(heapTermName).get.term
          else throw NeedsHeapModelException

        def sortWrapper(s: Sort): Option[MonoSortedIFunction] =
          sortWrapperMap.get(s)

        def sortGetter(s: Sort): Option[MonoSortedIFunction] =
          sortGetterMap.get(s)

        def getTypOfPointer(t: CCType): CCType = t match {
          case p: CCHeapPointer => p.typ
          case t => t
        }

        def getCtor(s: Sort): Int = sortCtorIdMap(s)

        override implicit val arithMode: CCReader.ArithmeticMode.Value =
          arithmeticMode
      }

      val funContext = new FunctionContext(prePred, postPred,
        new ReaderFunctionContext, prePredArgACSLNames, postPredACSLArgNames)
      functionContexts += ((funDef.name, funContext))
    }

    val annotatedFuns : Map[Afunc, FunctionContract] =
      for ((fun, annots) <- funsThatMightHaveACSLContracts;
           annot <- annots if annot.isInstanceOf[MaybeACSLAnnotation]) yield {

        val name = getName(fun.function_def_)
        val funContext = functionContexts(name)
        val possibleACSLAnnotation = annot.asInstanceOf[MaybeACSLAnnotation]
        // todo: try / catch and print msg?
        val contract = ACSLTranslator.translateACSL(
          "/*@" + possibleACSLAnnotation.annot + "*/", funContext.acslContext)

        prePredsToReplace.add(funContext.prePred.pred)
        postPredsToReplace.add(funContext.postPred.pred)
        funToPreAtom.put(name, atom(funContext.prePred))
        funToPostAtom.put(name, atom(funContext.postPred))
        funsWithAnnot.add(name)
        val funContract = contract.asInstanceOf[FunctionContract]
        funToContract.put(name, funContract)

        (fun, funContract)
      }

    // ... and generate clauses for those functions
    for (f <- (contractFuns ++ annotatedFuns.keys).distinct) {
      import HornClauses._

      val funDef = FuncDef(f.function_def_)
      val name = funDef.name
      val typ = getType(f.function_def_)
      val funContext = functionContexts(name)
      val (prePred, postPred) = (funContext.prePred, funContext.postPred)
      setPrefix(name)

      localVars.pushFrame
      val stm = pushArguments(f.function_def_)

      val prePredArgs = allFormalVarTerms.toList

      for (v <- functionPostOldArgs(name)) localVars addVar v

      val entryPred = newPred(Nil, Some(getSourceInfo(f)))

      val resVar = getResVar(typ)
      val exitPred = newPred(resVar, Some(getLastSourceInfo(funDef.body)))

      output(entryPred(prePredArgs ++ prePredArgs) :- prePred(prePredArgs))

      val translator = FunctionTranslator(exitPred)
      val finalPred = typ match {
        case _ : CCVoid =>
          translator.translateNoReturn(stm, entryPred)
          exitPred
        case _          =>
          translator.translateWithReturn(stm, entryPred)
      }

      functionExitPreds += ((name, finalPred))

      val globalVarTerms : Seq[ITerm] = globalVars.formalVarTerms
      val postArgs : Seq[ITerm] = (allFormalVarTerms drop prePredArgs.size) ++
        globalVarTerms ++ resVar.map(v => IConstant(v.term))

      output(postPred(postArgs) :- exitPred(allFormalVarTerms ++
                                   resVar.map(v => IConstant(v.term))))

      if (timeInvariants nonEmpty)
        throw new TranslationException(
          "Contracts cannot be used for functions with time invariants")
      if (clauses exists (_._2 != ParametricEncoder.NoSync))
        throw new TranslationException(
          "Contracts cannot be used for functions using communication channels")

      functionClauses.put(name, functionClauses.getOrElse(name, Nil) ++ clauses)
      functionAssertionClauses.put(name,
        functionAssertionClauses.getOrElse(name, Nil) ++ assertionClauses)

      clauses.clear
      assertionClauses.clear

      localVars popFrame
    }

    // then translate the threads
    atomicMode = false

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Athread =>
          decl.thread_def_ match {
            case thread : SingleThread => {
              setPrefix(thread.cident_)
              val translator = FunctionTranslator.apply
              val finalPred = translator translateNoReturn(thread.compound_stm_)
              functionExitPreds += ((thread.cident_, finalPred))
              processes += ((clauses.toList, ParametricEncoder.Singleton))
              clauses.clear
            }
            case thread : ParaThread => {
              setPrefix(thread.cident_2)
              localVars pushFrame
              val threadVar = new CCVar(thread.cident_1,
                Some(getSourceInfo(thread)),
                CCInt())
              localVars addVar threadVar
              val translator = FunctionTranslator.apply
              val finalPred = translator translateNoReturn(thread.compound_stm_)
              functionExitPreds += ((thread.cident_2, finalPred))
              processes += ((clauses.toList, ParametricEncoder.Infinite))
              clauses.clear
              localVars popFrame
            }
          }

        case _ =>
          // nothing
      }

    if (functionClauses contains entryFunction) {
      hasACSLEntryFunction = true
      // do not encode entry function clauses if they are already generated
      processes +=
        ((functionClauses(entryFunction), ParametricEncoder.Singleton))
      assertionClauses ++= functionAssertionClauses(entryFunction)
      functionClauses remove entryFunction
      functionAssertionClauses remove entryFunction
    }
    else {
      // is there a global entry point in the program?
      (functionDefs get entryFunction) match {
        case Some(funDef) => {
          setPrefix(entryFunction)

          localVars pushFrame

          val f = FuncDef(funDef)

          val returnType = {
            FuncDef(funDef).declSpecs match {
              case Some(declSpec) => getType(declSpec)
              case None => CCVoid()
            }
          }

          val exitVar = getResVar(returnType)
          val exitPred = newPred(exitVar, Some(getLastSourceInfo(f.body)))

          val stm = pushArguments(funDef)

          val translator = FunctionTranslator(exitPred)
          val finalPred =
            if (!returnType.isInstanceOf[CCVoid]) {
              translator.translateWithReturn(stm)
              exitPred
            }
            else
              translator.translateNoReturn(stm)

          functionExitPreds += ((f.name, finalPred))

          // add an assertion to track memory safety (i.e., no memory leaks)
          // currently this is only added to the exit point of the entry function,
          if (modelHeap && trackMemorySafety) {
            import HornClauses._
            import IExpression._
            finalPred match {
              case CCPredicate(_, args, _) if args.head.sort == heap.HeapSort =>
                // passing sort as CCVoid as it is not important
                val addrVar = getFreshEvalVar(CCHeapPointer(heap, CCVoid()))
                val resVar = getResVar(args.last.typ)
                var excludedAddresses = i(true)
                for (arg <- args) arg.typ match {
                  case arr: CCHeapArrayPointer if arr.arrayLocation == GlobalArray =>
                    excludedAddresses = excludedAddresses &&&
                      !heap.within(arg.term, addrVar.term)
                  case _ => // nothing
                }
                assertionClauses += CCClause(
                  ((heap.read(args.head.term, addrVar.term) === defObj()) :- (atom(finalPred.pred, allFormalVarTerms.toList ++
                  resVar.map(v => IConstant(v.term))) &&& excludedAddresses)),
                  None) // todo: add proper line numbers for auto-added free assertions
              case _ => throw new TranslationException("Tried to add -memtrack" +
                "assertion but could not find the heap term!")
            }
          }

          processes += ((clauses.toList, ParametricEncoder.Singleton))
          clauses.clear

          localVars popFrame
        }
        case None =>
          warn("entry function \"" + entryFunction + "\" not found")
      }
    }

    // remove assertions that are no longer connected to predicates
    // actually occurring in the system

    val allPreds =
      (for ((cls, _) <- processes.iterator;
            (c, _) <- cls.iterator;
            p <- c.predicates.iterator)
       yield p).toSet

    val remainingAssertions =
      assertionClauses filter { c => c.clause.bodyPredicates subsetOf allPreds }
    assertionClauses.clear
    assertionClauses ++= remainingAssertions
  }

  //////////////////////////////////////////////////////////////////////////////
  private def collectStructDefs(dec : Dec) : Unit = {
    dec match {
      case decl : Declarators => { // todo: check for multiple type specs
        val typ = decl.listdeclaration_specifier_.find(_.isInstanceOf[Type]) match {
          case Some(t) => t.asInstanceOf[Type].type_specifier_
          case None => throw new
              TranslationException("Could not determine type for " + decl)
        }
        typ match {
          case structDec : Tstruct =>
            structDec.struct_or_union_spec_ match {
              case _: Unique =>
                val declarator = decl.listinit_declarator_.head match {
                  case initDecl: OnlyDecl     => initDecl.declarator_
                  case initDecl: HintDecl     => initDecl.declarator_
                  case initDecl: InitDecl     => initDecl.declarator_
                  case initDecl: HintInitDecl => initDecl.declarator_
                }
                collectStructInfo(structDec)
              case _ => collectStructInfo(structDec) // use X in "struct X"
            }
          case _ => // do nothing
        }
      }
      case nodecl : NoDeclarator => {
        val typ = nodecl.listdeclaration_specifier_(0) match {
          case spec: Type => spec.type_specifier_
          case _ => throw new
              TranslationException("Storage and SpecProp not implemented yet")
        }
        typ match {
          case structSpec : Tstruct =>
            val structName = getStructName(structSpec)
            if (structSpec.struct_or_union_spec_.isInstanceOf[TagType])
              structInfos += StructInfo(structName, List())
            else collectStructInfo(structSpec)
          case enumDec : Tenum => buildEnumType(enumDec)
          case _ =>
        }
      }
      case preddecl : PredDeclarator => // nothing
    }
  }

  private def isUniqueStruct(listDec : ListDeclaration_specifier) : Boolean = {
    if (listDec.nonEmpty) {
      listDec.head.isInstanceOf[Type] &&
        listDec.head.asInstanceOf[Type].type_specifier_.isInstanceOf[Tstruct] &&
        listDec.head.asInstanceOf[Type].type_specifier_.asInstanceOf[Tstruct].
          struct_or_union_spec_.isInstanceOf[Unique]
    } else false
  }

  case object InitDeclaratorWrapper {
    def apply(initDecl : Init_declarator) : InitDeclaratorWrapper = {
      val srcInfo = getSourceInfo(initDecl)
      initDecl match {
        case initDecl : OnlyDecl => InitDeclaratorWrapper(
          initDecl.declarator_, None, Nil, srcInfo)
        case initDecl : HintDecl =>
          InitDeclaratorWrapper(
            initDecl.declarator_, None, initDecl.listannotation_, srcInfo)
        case initDecl : InitDecl => InitDeclaratorWrapper(
          initDecl.declarator_, Some(initDecl.initializer_), Nil, srcInfo)
        case initDecl : HintInitDecl => InitDeclaratorWrapper(
          initDecl.declarator_, Some(initDecl.initializer_), initDecl.listannotation_,
          srcInfo)
      }
    }
  }
  case class InitDeclaratorWrapper(declarator       : Declarator,
                                   maybeInitializer : Option[Initializer],
                                   hints            : Seq[Annotation],
                                   sourceInfo       : SourceInfo)

  sealed abstract class CCDeclaration
  // todo: better handling of function declarations
  case class CCFunctionDeclaration(name       : String,
                                   typ        : CCType,
                                   directDecl : Direct_declarator,
                                   srcInfo    : SourceInfo) extends CCDeclaration
  case class CCVarDeclaration(name             : String,
                              typ              : CCType,
                              maybeInitializer : Option[Initializer],
                              hints            : Seq[Annotation],
                              isArray          : Boolean,
                              needsHeap        : Boolean,
                              initArrayExpr    : Option[Constant_expression],
                              srcInfo          : SourceInfo) extends CCDeclaration
  case object CCNoDeclaration extends CCDeclaration
  case class CCPredDeclaration(predHints : ListPred_hint,
                               srcInfo   : SourceInfo) extends CCDeclaration

  private[concurrency]
  def collectVarDecls(dec : Dec, isGlobal : Boolean) : Seq[CCDeclaration] = {
    dec match {
      case decl: Declarators => {
        // S D1, D2, D3, ...
        // in C, the type of a variable is the spec type that can be further
        //   modified in init declarators. Above S is the specType.
        // example: int x1, *x2, *x3[];
        // first one is an int, second one is an int*, last is an array of int*s
        val specType = getType(decl.listdeclaration_specifier_)

        // each iteration is for one of the initDecls, above D1, D2, D3
        for (initDecl <- decl.listinit_declarator_) yield {
          val initDeclWrapper = InitDeclaratorWrapper(initDecl)
          val name = getName(initDeclWrapper.declarator)
          val (typeWithPtrs, directDecl) = initDeclWrapper.declarator match {
            case decl: NoPointer =>
              (specType, decl.direct_declarator_)
            case decl: BeginPointer =>
              (getPtrType(decl.pointer_, specType), decl.direct_declarator_)
          }
          directDecl match {
            // function declaration
            case _: NewFuncDec /* | _ : OldFuncDef */ | _: OldFuncDec =>
              CCFunctionDeclaration(name, typeWithPtrs, directDecl,
                initDeclWrapper.sourceInfo) // todo: check that typeWithPtrs is correct here
            // array declaration
            case _: InitArray | _: Incomplete if !TriCeraParameters.parameters.value.useArraysForHeap =>
              val (arrayType, initArrayExpr) = {
                val (arrayLocation, initArrayExpr) = directDecl match {
                  case a: InitArray if isGlobal =>
                    (GlobalArray, Some(a.constant_expression_))
                  case a: InitArray if !isGlobal =>
                    (StackArray, Some(a.constant_expression_))
                  case _ => (HeapArray, None)
                }
                (CCHeapArrayPointer(heap, typeWithPtrs, arrayLocation), initArrayExpr)
              }
              // todo: adjust needsHeap below if an array type does not require heap
              // for instance if we model arrays using the theory of arrays or unroll
              CCVarDeclaration(name, arrayType, initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = true, needsHeap = true,
                initArrayExpr = initArrayExpr, srcInfo = initDeclWrapper.sourceInfo)
            case _: InitArray | _: Incomplete if TriCeraParameters.parameters.value.useArraysForHeap =>
              val (arrayType, initArrayExpr) = {
                val (arrayLocation, initArrayExpr) = directDecl match {
                  case a: InitArray if isGlobal =>
                    (GlobalArray, Some(a.constant_expression_))
                  case a: InitArray if !isGlobal =>
                    (StackArray, Some(a.constant_expression_))
                  case _ => (HeapArray, None)
                }
                (CCArray(typeWithPtrs, None, None, ExtArray(Seq(CCInt().toSort), typeWithPtrs.toSort), arrayLocation), initArrayExpr)
              }
              // todo: adjust needsHeap below if an array type does not require heap
              // for instance if we model arrays using the theory of arrays or unroll
              CCVarDeclaration(name, arrayType, initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = true, needsHeap = false,
                initArrayExpr = initArrayExpr, srcInfo = initDeclWrapper.sourceInfo)
            case _ : MathArray =>
              CCVarDeclaration(name, CCArray(typeWithPtrs, None, None,
                ExtArray(Seq(CCInt().toSort), typeWithPtrs.toSort), if(isGlobal) GlobalArray else HeapArray),
                initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = true, needsHeap = false,
                initArrayExpr = None, srcInfo = initDeclWrapper.sourceInfo)
            case _: Name =>
              CCVarDeclaration(name, typeWithPtrs, initDeclWrapper.maybeInitializer,
                initDeclWrapper.hints, isArray = false, needsHeap = false,
                initArrayExpr = None, srcInfo = initDeclWrapper.sourceInfo)
          }
        }
      }
      case noDecl: NoDeclarator =>
        Seq(CCNoDeclaration)
      case predDecl: PredDeclarator =>
        Seq(CCPredDeclaration(predDecl.listpred_hint_, getSourceInfo(predDecl)))
    }
  }

  private def collectVarDecls(dec : Dec,
                              global : Boolean,
                              values : Symex) : Unit = {
    val decls = collectVarDecls(dec, global)
    for (decl <- decls) decl match {
      case funDec : CCFunctionDeclaration =>
        functionDecls.put(funDec.name, (funDec.directDecl, funDec.typ))
      case varDec : CCVarDeclaration =>
        if(!modelHeap && varDec.needsHeap)
          throw NeedsHeapModelException

        val lhsVar = new CCVar(varDec.name, Some(varDec.srcInfo), varDec.typ)
        val srcInfo = lhsVar.srcInfo

        val (actualLhsVar, initValue, initGuard) =
          varDec.maybeInitializer match {
            case Some(init : InitExpr) =>
              if (init.exp_.isInstanceOf[Enondet]) {
                (lhsVar, CCTerm(lhsVar.term, varDec.typ, srcInfo),
                  lhsVar rangePred)
              } else {
                // discard useless type conversions
                val actualInitExp = init.exp_ match {
                  case typeConv : Etypeconv
                    if getType(typeConv.type_name_) == lhsVar.typ =>
                    typeConv.exp_
                  case _ => init.exp_
                }

                if (varDec.typ.isInstanceOf[CCHeapArrayPointer])
                  values.lhsIsArrayPointer = true // todo: find smarter solution!
                val res = values eval actualInitExp
                values.lhsIsArrayPointer = false
                val (actualLhsVar, actualRes) = lhsVar.typ match {
                  case _ : CCHeapPointer if res.typ.isInstanceOf[CCArithType] =>
                    if(res.toTerm.asInstanceOf[IIntLit].value.intValue == 0)
                      (lhsVar, CCTerm(heap.nullAddr(), varDec.typ, srcInfo))
                    else throw new TranslationException("Pointer arithmetic is not " +
                      "allowed, and the only possible initialization value for " +
                      "pointers is 0 (NULL)")
                  case _ : CCHeapPointer if res.typ.isInstanceOf[CCHeapArrayPointer] =>
                    // lhs is actually a heap array pointer
                    (new CCVar(lhsVar.name, lhsVar.srcInfo, res.typ), res)
                  case _ : CCHeapPointer if res.typ.isInstanceOf[CCStackPointer] =>
                    // lhs is actually a stack pointer
                    (new CCVar(lhsVar.name, lhsVar.srcInfo, res.typ), res)
                  case _ => (lhsVar, res)
                }
                (actualLhsVar, actualRes, IExpression.i(true))
              }
            case Some(_ : InitListOne) | Some(_: InitListTwo) => {
              val initStack =
                getInitsStack(varDec.maybeInitializer.get, values)
              varDec.typ match {
                case structType : CCStruct =>
                  (lhsVar, CCTerm(structType.getInitialized(initStack), varDec.typ, srcInfo),
                    lhsVar rangePred)
                case arrayPtr : CCHeapArrayPointer =>
                  val addressRangeValue = varDec.initArrayExpr match {
                    case Some(expr) =>
                      val arraySizeTerm =
                        values eval expr.asInstanceOf[Especial].exp_
                      val arraySize = arraySizeTerm match {
                        case CCTerm(IIntLit(IdealInt(n)), actualType, srcInfo)
                          if actualType.isInstanceOf[CCArithType] => n
                        case _ => throw new TranslationException(
                          "Array with non-integer" +
                            "size specified in an intialized array expression!")
                      }
                      import IExpression._
                      val initHeapTerm =
                        if (values.getValues.head.toTerm == IConstant(heapTerm)) {
                          CCTerm(globalVars.inits.head.toTerm, CCHeap(heap), srcInfo)
                        } else
                          CCTerm(values.getValues.head.toTerm, CCHeap(heap), srcInfo)
                      val objTerm = CCTerm(arrayPtr.elementType.getZeroInit,
                        arrayPtr.elementType, srcInfo)
                      val arrayTerm =
                        values.heapBatchAlloc(objTerm, arraySizeTerm.toTerm, initHeapTerm)
                      def getInitializedObj = {
                        if (initStack.nonEmpty) {
                          arrayPtr.elementType match {
                            case structType: CCStruct =>
                              structType.getInitialized(initStack)
                            case _ => initStack.pop // todo: union types, array types
                          }
                        }
                        else arrayPtr.elementType.getZeroInit
                      }
                      for(i <- 0 until arraySize)
                        values.heapWrite(heap.nth(arrayTerm, i),
                          getInitializedObj, arrayPtr.elementType.toSort)
                      arrayTerm
                    case None =>
                      throw new TranslationException("Cannot initialize" +
                        "arrays with unknown size")
                  }
                  // initialise using the first address of the range
                  (lhsVar, CCTerm(addressRangeValue, varDec.typ, srcInfo), IExpression.i(true))
                case s =>
                  println(s)
                  throw new TranslationException("Union list " +
                    "initialization is not yet supported.")
              }
            }
            case Some(_) => throw new TranslationException("Unsupported" +
              "initializer expression.")
            case None =>
              varDec.typ match {
                case typ : CCHeapArrayPointer =>
                  val objValue = if (global) typ.elementType.getZeroInit
                  else typ.elementType.getNonDet
                  val objTerm = CCTerm(objValue, typ.elementType, srcInfo)
                  val initHeapTerm =
                    if (values.getValues.head.toTerm == IConstant(heapTerm)) {
                      CCTerm(globalVars.inits.head.toTerm, CCHeap(heap), srcInfo)
                    } else
                      CCTerm(values.getValues.head.toTerm, CCHeap(heap), srcInfo)
                  val addressRangeValue = varDec.initArrayExpr match {
                    case Some(expr) =>
                      val arraySize = values eval expr.asInstanceOf[Especial].exp_
                      values.heapBatchAlloc(objTerm, arraySize.toTerm, initHeapTerm)
                    case None =>
                      heap.addressRangeCtor(heap.nullAddr(), IIntLit(0))
                  }
                  // initialise using the first address of the range
                  (lhsVar, CCTerm(addressRangeValue, typ, srcInfo), IExpression.i(true))
                case _ if global =>
                  (lhsVar, CCTerm(varDec.typ.getZeroInit, varDec.typ, srcInfo),
                    lhsVar rangePred)
                case _ =>
                  (lhsVar, CCTerm(lhsVar.term, varDec.typ, srcInfo),
                    lhsVar rangePred)
              }
          }

        // do not use actualType below, take from lhsVar

        if (global) {
          globalVars addVar actualLhsVar
          variableHints += List()
        } else {
          localVars addVar actualLhsVar
        }

        actualLhsVar.typ match {
          case _ : CCClock =>
            values addValue translateClockValue(initValue)
          case _ : CCDuration =>
            values addValue translateDurationValue(initValue)
          case _ =>
            values addValue (actualLhsVar.typ cast initValue)
        }

        values addGuard (
          if(varDec.typ == actualLhsVar.typ) initGuard
          else actualLhsVar rangePred
        )

        // parse possible model checking hints
        processHints(varDec.hints)

      case predDec : CCPredDeclaration =>
        for (hint <- predDec.predHints) {
          hint match {
            case predHint : PredicateHint =>
              val argTypes =
                for (typ <- predHint.listtype_specifier_) yield getType(typ)
              val argCCVars = // needed for adding to predCCPredMap, used in printing
                argTypes.zipWithIndex.map(t => new CCVar("_" + t._2, None, t._1))
              val hintPred = newPred(predHint.cident_, argCCVars, None) // todo: line no for unint preds?
              uninterpPredDecls += ((predHint.cident_, hintPred))
          }
        }
      case CCNoDeclaration => // todo: nothing?
    }
  }

  private def processHints(hintAnnotations : Seq[Annotation]) : Unit = {
    val hints : Seq[AbsHintClause] = (for (hint <- hintAnnotations) yield {
      AnnotationParser(hint)
    }).flatten.filter(_.isInstanceOf[AbsHintClause]).
      map(_.asInstanceOf[AbsHintClause])
    if (hints.nonEmpty) {
      val hintSymex = Symex(null)
      hintSymex.saveState

            val subst =
              (for ((v, n) <-
                      (globalVars.iterator ++ localVars.iterator).zipWithIndex)
               yield (v.term.asInstanceOf[ConstantTerm] -> IExpression.v(n))).toMap

      import AnnotationParser._
      val hintEls =
        for (hint <- hints;
             cost = hint.cost.getOrElse("1").toInt;
             e <- hint.exp_args match {
               case Some(args) => inAtomicMode(hintSymex evalList args)
               case None => Nil
             })
              yield hint.hint match {
                case Predicates => {
                  usingInitialPredicates = true
                  VerifHintInitPred(ConstantSubstVisitor(e.toFormula, subst))
                }
                case PredicatesTpl =>
                  VerifHintTplPred(ConstantSubstVisitor(e.toFormula, subst),
                                   cost)
                case TermsTpl =>
                  VerifHintTplEqTerm(ConstantSubstVisitor(e.toTerm, subst),
                                     cost)
                case _ =>
                  throw new TranslationException("cannot handle hint " +
                                                 hint.hint)
              }

            if (!hintSymex.atomValuesUnchanged)
              throw new TranslationException(
                "Hints are not side effect-free: " +
                hints.mkString(""))

            variableHints(variableHints.size - 1) = hintEls
          }
    }

  private def getName (f : Function_def) : String = getName(FuncDef(f).decl)

  private def getName(decl : Declarator) : String = decl match {
    case decl : NoPointer => getName(decl.direct_declarator_)
    case decl : BeginPointer => getName(decl.direct_declarator_)
  }

  private def getName(decl : Direct_declarator) : String = decl match {
    case decl : Name      => decl.cident_
    case decl : ParenDecl => getName(decl.declarator_)
    case dec : NewFuncDec => getName(dec.direct_declarator_)
//    case dec : OldFuncDef => getName(dec.direct_declarator_)
    case dec : OldFuncDec => getName(dec.direct_declarator_)
    case dec : InitArray => getName(dec.direct_declarator_)
    case dec : Incomplete => getName(dec.direct_declarator_)
    case dec : MathArray => getName(dec.direct_declarator_)
  }

  private def getType(specs : Seq[Declaration_specifier]) : CCType =
    getType(for (specifier <- specs.iterator;
                 if (specifier.isInstanceOf[Type]))
            yield specifier.asInstanceOf[Type].type_specifier_)

  private def getPtrType (ptr : Pointer, _typ : CCType) : CCType = {
    ptr match {
      case _   : Point => CCHeapPointer(heap, _typ)
      case ptr : PointPoint =>
        getPtrType(ptr.pointer_, CCHeapPointer(heap, _typ))
      case _ => throw new TranslationException(
        "Advanced pointer declarations are not yet supported (line " +
          getSourceInfo(ptr).line + ")"
      )
    }
  }

  private def getType(name : Type_name) : CCType = name match {
    case name : PlainType =>
      getType(for (qual <- name.listspec_qual_.iterator;
                   if (qual.isInstanceOf[TypeSpec]))
              yield qual.asInstanceOf[TypeSpec].type_specifier_)
    case name : ExtendedType =>
      val typ = getType(for (qual <- name.listspec_qual_.iterator;
                   if (qual.isInstanceOf[TypeSpec]))
        yield qual.asInstanceOf[TypeSpec].type_specifier_)
      name.abstract_declarator_ match {
        case ptr: PointerStart => getPtrType(ptr.pointer_, typ)
        case _ => throw new TranslationException(
          "Advanced declarators are not yet supported: " + name
        )
      }
  }

  private def getType(exp : Ebytestype) : CCType = getType(exp.type_name_)

  // get type of struct field
  private def getType(fields : Struct_dec) : CCType = {
    val specs =
      (for (qual <- fields.asInstanceOf[Structen].listspec_qual_.iterator;
           if (qual.isInstanceOf[TypeSpec]))
        yield qual.asInstanceOf[TypeSpec].type_specifier_).toList
    specs.find(s => s.isInstanceOf[Tenum]) match {
      case Some(enum) => buildEnumType(enum.asInstanceOf[Tenum])
      case None =>
        val (maybeDecl, maybeConstExpr) =
          fields.asInstanceOf[Structen].liststruct_declarator_.head match {
            case f : Decl =>
              (Some(f.declarator_), None)
            case f : Field =>
              (None, f.constant_expression_)
            case f : DecField =>
              (Some(f.declarator_), Some(f.constant_expression_))
          }

        val typ = getType(specs.toIterator)
        // todo: unify this with code from collectVarDecl
        val actualTyp = if (maybeDecl isEmpty) {
          typ
        } else {
          val (directDecl, isPointer, sourceInfo) = maybeDecl.get match {
            case decl: NoPointer => (decl.direct_declarator_, false,
              Some(SourceInfo(decl.line_num, decl.col_num, decl.offset)))
            case decl: BeginPointer => (decl.direct_declarator_, true,
              Some(SourceInfo(decl.line_num, decl.col_num, decl.offset)))
          }
          directDecl match {
            case _: NewFuncDec /* | _ : OldFuncDef */ | _: OldFuncDec =>
              throw new TranslationException("Functions as struct fields" +
                " are not supported.")
            case _: Incomplete if !TriCeraParameters.parameters.value.useArraysForHeap =>
              if (!modelHeap) throw NeedsHeapModelException
              CCHeapArrayPointer(heap, typ, HeapArray)
            case _: Incomplete if TriCeraParameters.parameters.value.useArraysForHeap =>
              CCArray(typ, None, None,
                ExtArray(Seq(CCInt().toSort), typ.toSort), HeapArray) // todo: only int indexed arrays
            case initArray: InitArray =>
              val arraySizeSymex = Symex(null)
              val arraySizeExp = arraySizeSymex eval
                initArray.constant_expression_.asInstanceOf[Especial].exp_
              val arraySize = arraySizeExp match {
                case CCTerm(IIntLit(IdealInt(n)), typ, srcInfo)
                  if typ.isInstanceOf[CCArithType] => n
                case _ => throw new TranslationException("Array with non-integer" +
                  "size specified inside struct definition!")
              }
              CCArray(typ, Some(arraySizeExp), Some(arraySize),
                ExtArray(Seq(arraySizeExp.typ.toSort), typ.toSort), HeapArray)
            case _ => typ
          }
        }
        actualTyp
    }
  }

  private var anonCount = 0
  private def getAnonName(prefix : String): String = {
    anonCount += 1
    prefix + (anonCount - 1)
  }

  private def getAnonStructName: String =
    getAnonName(".AS")

  private def getAnonEnumName: String =
    getAnonName(".ES")

  private def getStructName(spec: Tstruct) : String =
    spec.struct_or_union_spec_ match {
      case u : Unique => uniqueStructs.get(u) match {
        case Some(name) => name
        case None => throw new TranslationException("Unique struct was not" +
          " found!")
      }
      case tagged: Tag => tagged.cident_
      case tagged: TagType => tagged.cident_
    }

  private def collectStructInfo(spec: Tstruct) : Unit = {
    spec.struct_or_union_spec_ match {
      case _ : Unique => collectStructInfo(spec, getAnonStructName)
      case tagged : Tag => collectStructInfo(spec, tagged.cident_)
      case _ => // todo: do nothing for TagType
    }
  }

  private def collectStructInfo (spec: Tstruct,
                                 structName: String): Unit = {
    if (structInfos contains structName) //todo:what about shadowing?
      throw new TranslationException(
        "struct " + structName + " is already defined")

    val fields = spec.struct_or_union_spec_ match {
      case dec: Tag => dec.liststruct_dec_
      case dec: Unique =>
        uniqueStructs += ((dec, structName))
        dec.liststruct_dec_
      case _ => throw new TranslationException("struct can only be built" +
        "with Unique or Tag types!")
    }

    val fieldList : IndexedSeq[FieldInfo] = (for (field <- fields) yield {

      // ignoring all qual specs such as volatile, const etc.
      val specs : List[Type_specifier] =
        (for (f <- field.asInstanceOf[Structen].listspec_qual_
             if f.isInstanceOf[TypeSpec])
          yield f.asInstanceOf[TypeSpec].type_specifier_).toList

      // if specs has a struct or union field we cannot simply get the type,
      // as the field itself might be defining a struct or union
      val fieldType : Either[Integer, CCType] =
      specs.find(s => s.isInstanceOf[Tstruct]) match {
        case Some(ts) =>
          val t = ts.asInstanceOf[Tstruct]
          val typeName = t.struct_or_union_spec_ match {
            case _ : Unique =>
              val name = getAnonStructName
              collectStructInfo(t, name) // need to collect the struct info now
              //uniqueStructs += ((t, name))
              name
            case _ => getStructName(t)
          }
          structInfos.indexWhere(s => s.name == typeName) match {
            case -1 =>
              structInfos += StructInfo(typeName, List())
              Left(structInfos.size - 1)
            case i => Left(i)
          }
        // todo: get pointer depth
        /*case t : Tstruct if t.struct_or_union_spec_.isInstanceOf[TagType] &&
          (getStructName(t) == structName || structIsDeclared(getStructName(t))) &&
          field.asInstanceOf[Structen].liststruct_declarator_(0).asInstanceOf[Decl].declarator_.isInstanceOf[BeginPointer] =>
          CCDeclarationOnlyPointer(getStructName(t))
        //todo: some error handling here?
        case t : Tstruct if structInfos contains getStructName(t) =>
          getType(field)*/
        case _ => Right(getType(field))
      }
      val declarators = field.asInstanceOf[Structen].liststruct_declarator_

      for (decl <- declarators if !decl.isInstanceOf[Field]) yield {
        val declarator = decl match {
          case d : Decl => d.declarator_
          case d : DecField => d.declarator_ // ignore bit field, only collect decl
        }

        val fieldName = getName(declarator)
        val ptrDepth = declarator match {
          case _ : BeginPointer => 1 //todo:heap find out actual depth
          case _ => 0
        }
        FieldInfo(fieldName, fieldType, ptrDepth) // todo: deal with pointer fields
      }
    }).toList.flatten.toIndexedSeq

    /*val ADTFieldList : List[(String, ap.theories.ADT.OtherSort)] =
      for((fieldName, fieldType) <- fieldList)
        yield (fieldName, ADT.OtherSort(fieldType.toSort))*/

    structInfos.indexWhere(s => s.name == structName) match {
      case -1 => structInfos += StructInfo(structName, fieldList)
      case i  =>
        if (structInfos(i).fieldInfos.nonEmpty) throw new TranslationException(
          "Struct name " + structName + " is used in more than one location, " +
            "this is currently not supported. As a workaround, please make " +
            "sure that all structs have unique names (even shadowed ones).")
        structInfos(i) = StructInfo(structName, fieldList)
    }
  }
  private def getInitsStack(init: Initializer, s: Symex): Stack[ITerm] = {
    val initStack = new Stack[ITerm]
    def fillInit(init: Initializer) {
      init match {
        case init: InitExpr => initStack.push(s.eval(init.exp_).toTerm)
        case init: InitListOne => fillInits(init.initializers_)
        case init: InitListTwo => fillInits(init.initializers_)
      }
    }
    def fillInits(inits: Initializers) {
      inits match {
        case init: AnInit => fillInit(init.initializer_)
        case init: MoreInit => {
          fillInit(init.initializer_)
          fillInits(init.initializers_)
        }
      }
    }
    fillInit(init)
    initStack
  }

  private def getEnumType(spec: Tenum) : CCType =
    spec.enum_specifier_ match {
      case dec : EnumDec =>
        buildEnumType(dec.listenumerator_, getAnonEnumName)
      case named : EnumName =>
        buildEnumType(named.listenumerator_, named.cident_)
      case vared : EnumVar =>
        (enumDefs get vared.cident_) match {
          case Some(t) => t
          case None =>
            throw new TranslationException(
              "enum " + vared.cident_ + " is not defined")
        }
    }

    private def buildEnumType(spec: Tenum) : CCType = {
    spec.enum_specifier_ match {
      case dec : EnumDec =>
        buildEnumType(dec.listenumerator_, getAnonEnumName)
      case named : EnumName =>
        buildEnumType(named.listenumerator_, named.cident_)
      case _ => CCInt()
    }
  }

  private def buildEnumType (specs: Seq[Enumerator],
                             enumName: String) : CCType = {
    if (enumDefs contains enumName)
      throw new TranslationException(
        "enum " + enumName + " is already defined")

    def addEnumerator(name : String, t : CCExpr) = {
      if (enumeratorDefs contains name)
        throw new TranslationException(
          "enumerator " + name + " already defined")
      enumeratorDefs.put(name, t)
    }
    {
      // map the enumerators to integers directly
      var nextInd = IdealInt.ZERO
      var enumerators = new MHashMap[String, IdealInt]
      val symex = Symex(null) // a temporary Symex to collect enum declarations
      // to deal with fields referring to same-enum fields, e.g. enum{a, b = a+1}
      localVars pushFrame // we also need to add them as vars

      for (s <- specs) s match {
        case s : Plain => {
          val ind = nextInd
          nextInd = nextInd + 1
          val v = new CCVar(s.cident_,
            Some(SourceInfo(s.line_num, s.col_num, s.offset)), CCInt())
          localVars addVar v
          symex.addValue(CCTerm(IIntLit(ind), CCInt(), v.srcInfo))
          enumerators += ((s.cident_, ind))
        }
        case s : EnumInit => {
          val ind = translateConstantExpr(s.constant_expression_, symex).toTerm match {
            case IIntLit(v) => v
            case ITimes(IdealInt(-1), IIntLit(v)) => -v
            case IPlus(IIntLit(v1), IIntLit(v2)) => v1 + v2
            case _ =>
              throw new TranslationException("cannot handle enumerator " +
                                             (printer print s))
          }
          nextInd = ind + 1
          val v = new CCVar(s.cident_,
            Some(SourceInfo(s.line_num, s.col_num, s.offset)), CCInt())
          localVars addVar v
          symex.addValue(CCTerm(IIntLit(ind), CCInt(), v.srcInfo))
          enumerators += ((s.cident_, ind))
        }
      }

      localVars popFrame

      val newEnum = CCIntEnum(enumName, enumerators.toSeq)
      enumDefs.put(enumName, newEnum)

      for ((n, v) <- enumerators)
        addEnumerator(n, CCTerm(v, newEnum, None)) // todo: srcInfo?
      newEnum
    }
  }

  /*private def updateArraySize (arrayTyp : CCArray, decl : OnlyDecl) = {
    if (arraySizes contains arrayTyp)
      throw new TranslationException(
        "size of " + arrayTyp + " is already defined")

    val symex = Symex(null) // a temporary Symex to collect the array size

    /*val arraySize = decl match {
      case initArray : InitArray => // todo: maybe this can be calculated beforehand, so we actually have an integer constant here?
        Some(symex.eval(initArray.constant_expression_.asInstanceOf[Especial].exp_)) // todo: n-d arrays?
      case _ : Incomplete => None // no size information
    }*/
    arraySizes += ((arrayTyp, arraySize))
  }*/

  private def getType(typespec : Type_specifier) : CCType = {
    getType(Seq(typespec).iterator)
  }

  private def getType(specs : Iterator[Type_specifier]) : CCType = {
    // by default assume that the type is int
    var typ : CCType = CCInt()

    for (specifier <- specs)
      specifier match {
            case _ : Tvoid =>
              typ = CCVoid()
            case _ : Tint =>
              // ignore
            case _ : Tchar =>
              // ignore
            case _ : Tsigned =>
              typ = CCInt()
            case _ : Tunsigned =>
              typ = CCUInt()
            case _ : Tlong if typ.isInstanceOf[CCInt] =>
              typ = CCLong()
            case _ : Tlong if typ.isInstanceOf[CCUInt] =>
              typ = CCULong()
            case _ : Tlong if typ.isInstanceOf[CCLong] =>
              typ = CCLongLong()
            case _ : Tlong if typ.isInstanceOf[CCULong] =>
              typ = CCULongLong()
            case structOrUnion : Tstruct =>
              val structName = getStructName(structOrUnion)
              typ = structDefs get structName match {
                case None => throw new TranslationException(
                  "struct " + structName + " not found!")
                case Some(structType) => structType
              }
            case enum : Tenum =>
              typ = getEnumType(enum)
            case _ : Tclock => {
              if (!useTime)
                throw NeedsTimeException
              typ = CCClock()
            }
            case _ : Tduration => {
              if (!useTime)
                throw NeedsTimeException
              typ = CCDuration()
            }
            case x => {
              warn("type " + (printer print x) +
                   " not supported, assuming int")
              typ = CCInt()
            }
          }
    typ
  }

  private def getType(functionDef : Function_def) : CCType = {
    val f = FuncDef(functionDef)
    val typ = f.declSpecs match {
      case Some(listDeclSpecs) =>
        getType(listDeclSpecs)
      case None => CCInt()
    }
    if(f.decl.isInstanceOf[BeginPointer]) CCHeapPointer(heap, typ) // todo: can be stack pointer too, this needs to be fixed
    else typ
  }

  private def translateClockValue(expr : CCExpr) : CCExpr = {
    import IExpression._
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm(GT.term + GTU.term*(-v), CCClock(), expr.srcInfo)
      case t if (expr.typ.isInstanceOf[CCClock]) =>
        CCTerm(t, CCClock(), expr.srcInfo)
      case t if (expr.typ.isInstanceOf[CCDuration]) =>
        CCTerm(GT.term - t, CCClock(), expr.srcInfo)
      case t =>
        throw new TranslationException(
          "clocks can only be set to or compared with integers")
    }
  }

  private def translateDurationValue(expr : CCExpr) : CCExpr = {
    import IExpression._
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case _ if (expr.typ.isInstanceOf[CCDuration]) =>
        expr
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm(GTU.term*v, CCDuration(), expr.srcInfo)
      case t =>
        throw new TranslationException(
          "duration variable cannot be set or compared to " + t)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateConstantExpr(expr : Constant_expression,
                                    symex : Symex = Symex(null)) : CCExpr = {
    symex.saveState
    val res = symex eval expr.asInstanceOf[Especial].exp_
    if (!symex.atomValuesUnchanged)
      throw new TranslationException(
        "constant expression is not side-effect free")
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Symex {
    def apply(initPred : CCPredicate) = {
      val values = new ArrayBuffer[CCExpr]
      values ++= allFormalExprs
      new Symex(initPred, values)
    }
  }

  private def atom(pred : Predicate, args : Seq[ITerm]) =
    IAtom(pred, args take pred.arity)
  private def atom(ccPred : CCPredicate, args : Seq[ITerm]) : IAtom =
    atom(ccPred.pred, args)
  private def atom(ccPred : CCPredicate) : IAtom =
    atom(ccPred.pred, ccPred.argVars.map(_.term))

  private class Symex private (oriInitPred : CCPredicate,
                               values : Buffer[CCExpr]) {
    private var guard : IFormula = true

    def addGuard(f : IFormula) : Unit = {
      if(!noSideEffects) {
        guard = guard &&& f
        touchedGlobalState =
          touchedGlobalState || !freeFromGlobal(f)
      }
    }

    def getGuard = guard

    //todo:Heap get rid of this or change name
    def heapRead(ptrExpr : CCExpr, assertMemSafety : Boolean = true,
                 assumeMemSafety : Boolean = true) : CCTerm = {
      val (objectGetter, typ : CCType) = ptrExpr.typ match {
        case typ : CCHeapPointer => (sortGetterMap(typ.typ.toSort), typ.typ)
        case _ => throw new TranslationException(
          "Can only read from heap pointers! (" + ptrExpr + ")")
      }
      val readObj = heap.read(getValue(heapTermName).toTerm, ptrExpr.toTerm)
      if (assertMemSafety)
        assertProperty(heap.heapADTs.hasCtor(readObj, sortCtorIdMap(typ.toSort)),
          ptrExpr.srcInfo) // todo: add tester methods for user ADT sorts?
      // also add memory safety assumptions to the clause
      if (assertMemSafety && assumeMemSafety)
        addGuard(heap.heapADTs.hasCtor(readObj, sortCtorIdMap(typ.toSort)))
      CCTerm(objectGetter(readObj), typ, ptrExpr.srcInfo)
    }
    def heapAlloc(value : CCTerm) : CCTerm = {
      val objTerm = sortWrapperMap(value.typ.toSort)(value.toTerm)
      val newAlloc = heap.alloc(getValue(heapTermName).toTerm, objTerm)
      setValue(heapTerm.name, CCTerm(heap.newHeap(newAlloc), CCHeap(heap), value.srcInfo))
      CCTerm(heap.newAddr(newAlloc), CCHeapPointer(heap, value.typ), value.srcInfo)
    }
    // batch allocates "size" "objectTerm"s, returns the address range
    // if "initHeapTerm" is passed, that is used as the initial heap term
    def heapBatchAlloc(value : CCTerm, size : ITerm,
                       initHeapTerm : CCExpr = getValue(heapTermName)) : ITerm = {
      val newBatchAlloc =
        heap.batchAlloc(initHeapTerm.toTerm,
                        sortWrapperMap(value.typ.toSort)(value.toTerm), size)
      //val newAllocHeap = heap.batchAllocHeap(initHeapTerm.toTerm, objectTerm, size)
      //setValue(heapTerm.name, CCTerm(newAllocHeap, CCHeap(heap)))
      val newHeap = heap.newBatchHeap(newBatchAlloc)
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), value.srcInfo))
      //heap.batchAllocAddrRange(initHeapTerm.toTerm, objectTerm, size)
      heap.newAddrRange(newBatchAlloc)
    }
    def heapArrayRead(arrExpr  : CCExpr,
                      index    : CCExpr,
                      arrType  : CCHeapArrayPointer,
                      assertMemSafety : Boolean = true,
                      assumeMemSafety : Boolean = true,
                      assertIndexWithinBounds : Boolean = true) : CCTerm = {
      import IExpression._
      val readAddress = CCTerm(heap.nth(arrExpr.toTerm, index.toTerm),
        CCHeapPointer(heap, arrType.elementType), arrExpr.srcInfo)
      val readValue = heapRead(readAddress, assertMemSafety, assumeMemSafety)
      if (assertIndexWithinBounds)
        assertProperty(heap.within(arrExpr.toTerm, readAddress.toTerm), arrExpr.srcInfo)
      readValue
    }

    /**
     * updates an Object on the heap, which can also be an ADT
     * @param lhs this must be a read from the location to be updated.
     *            e.g. getInt(read(h,a)) or an ADT selector x(getS(read(h,a)))
     * @param rhs the term to be written to the location pointed by lhs
     * @param assertMemSafety add memory safety assertion
     * @param assumeMemSafety assume memory safety after write
     */
    def heapWrite(lhs : IFunApp, rhs : CCExpr,
                  assertMemSafety : Boolean = false,
                  assumeMemSafety : Boolean = false) = {
      val newHeap = heap.writeADT(lhs, rhs.toTerm).asInstanceOf[IFunApp]
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), rhs.srcInfo))
      if (assertMemSafety) {
        def getObjAndSort(f : IFunApp) : (IFunApp, Sort) = {
          if (objectGetters contains f.fun) {
            val sort = f.fun.asInstanceOf[MonoSortedIFunction].resSort
            val obj = f.args.head.asInstanceOf[IFunApp]
            (obj, sort)
          } else if (f.args.size == 1 && f.args.head.isInstanceOf[IFunApp]) {
            getObjAndSort(f.args.head.asInstanceOf[IFunApp])
          } else
            throw new TranslationException("Cannot determine read" +
              "object from passed term")
        }
        val (writtenObj, sort) = getObjAndSort(lhs)

        assertProperty(heap.heapADTs.hasCtor(writtenObj, sortCtorIdMap(sort)),
          rhs.srcInfo) // todo: add tester methods for user ADT sorts?
        // also add memory safety assumptions to the clause
        if (assumeMemSafety)
          addGuard(heap.heapADTs.hasCtor(writtenObj, sortCtorIdMap(sort)))
      }
    }

    /**
     * Write the passed object to the passed location on the heap
     */
      // todo: add mem-/type-safety assertions?
    def heapWrite(addr : ITerm, obj : ITerm, objSort : Sort) = {
      val heapVal = getValue(heapTerm.name)
      val newHeap = heap.write(heapVal.toTerm, addr, sortWrapperMap(objSort)(obj))
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), None)) // todo: src info?
    }

    def heapBatchWrite(h : ITerm, r : ITerm, o : ITerm) = {
      val newHeap = heap.batchWrite(h, r, o)
      setValue(heapTerm.name, CCTerm(newHeap, CCHeap(heap), None)) // todo: src info?
    }

    def heapFree(t : CCExpr) = {
      t.typ match {
        case p : CCHeapPointer =>
          val termToFree : IFunApp =
            heapRead(t, assertMemSafety = false).toTerm match {
              case IFunApp(f, Seq(arg)) if (objectGetters contains f) &
                arg.isInstanceOf[IFunApp] =>
                arg.asInstanceOf[IFunApp]
              case _ => throw new TranslationException("Could not resolve" +
                " the term to free: " + t)
            }
          heapWrite(termToFree, CCTerm(p.heap._defObj, p, t.srcInfo))
        case p : CCHeapArrayPointer =>
          import IExpression._
          //val n = getFreshEvalVar(CCUInt())
          //addGuard(n.term >= 0 & n.term < heap.addrRangeSize(t.toTerm))
          //val a = getFreshEvalVar(CCHeapPointer(heap, p.elementType))
          //addGuard(heap.within(t.toTerm, a.term))
          /*val termToFree : IFunApp =
            heapRead(CCTerm(a.term, a.typ),
                     assertMemSafety = false).toTerm match {
              case IFunApp(f, Seq(arg)) if (objectGetters contains f) &
                                            arg.isInstanceOf[IFunApp] =>
                arg.asInstanceOf[IFunApp]
              case _ => throw new TranslationException("Could not resolve" +
                " the term to free: " + t)
            }
          heapWrite(termToFree, CCTerm(p.heap._defObj, p))*/
          // todo: what about ADTs?
          //if(p.arrayType != HeapArray) throw new TranslationException("Trying to free global or stack pointer " + p)
          // todo: unsafe instead of exception?
          heapBatchWrite(getValue(heapTermName).toTerm, t.toTerm, defObj())
        case _ => throw new TranslationException("Unsupported operation: " +
          "trying to free " + t + ".")
      }
    }

    private var initAtom =
      if (oriInitPred == null)
        null
      else
        atom(oriInitPred, allFormalVarTerms)
    private def initPred = predCCPredMap(initAtom.pred)

    def initAtomArgs = if(initAtom != null) Some(initAtom.args) else None

    private val savedStates = new Stack[(IAtom, Seq[CCExpr], IFormula, /*IFormula,*/ Boolean)]
    def saveState =
      savedStates push ((initAtom, values.toList, guard, touchedGlobalState))
    def restoreState = {
      val (oldAtom, oldValues, oldGuard, /*oldPullGuard,*/ oldTouched) = savedStates.pop
      initAtom = oldAtom
      values.clear
      oldValues copyToBuffer values
      localVars.pop(localVars.size - values.size + globalVars.size)
      guard = oldGuard
      touchedGlobalState = oldTouched
    }

    def atomValuesUnchanged = {
      val (oldAtom, oldValues, _, /*_,*/ _) = savedStates.top
      initAtom == oldAtom &&
      ((values.iterator zip oldValues.iterator) forall {
         case (x, y) => x == y
       })
    }

    private var touchedGlobalState : Boolean = false
    private var assignedToStruct : Boolean = false

    private def maybeOutputClause : Unit =
      if (!noSideEffects &&
        ((!atomicMode && touchedGlobalState) || assignedToStruct)) outputClause

    private def pushVal(v : CCExpr) = {
      val freshVar = getFreshEvalVar(v.typ)
      addValue(v)
      // reserve a local variable, in case we need one later
      localVars addVar freshVar

      if (usingInitialPredicates) {
        // if the pushed value refers to other variables,
        // add initial predicates that relate the values of
        // temporary variables with the original variables
        //
        // TODO: this is currently not very effective ...

        val varMapping =
          (for (d <- v.occurringConstants.iterator;
                index = lookupVarNoException(d.name))
           yield (d -> index)).toMap

        if (varMapping forall { case (_, ind) => ind >= 0 }) {
          val defTerm =
            ConstantSubstVisitor(v.toTerm,
                                 varMapping mapValues (IExpression.v(_)))
          val rhs = IExpression.v(variableHints.size - 1)

          if (defTerm != rhs) {
            val defEq = defTerm === rhs
            variableHints(variableHints.size - 1) =
              List(VerifHintInitPred(defEq))
          }
        }
      }
    }

    private def pushFormalVal(typ : CCType) = {
      val freshVar = getFreshEvalVar(typ)
      localVars addVar freshVar
      addValue(CCTerm(freshVar.term, typ, None)) // todo: srcInfo?
      addGuard(freshVar rangePred)
    }

    private def popVal = {
      val res = values.last
      values trimEnd 1
      localVars.pop(1)
      res
    }
    private def topVal = values.last
    private def removeVal(ind : Int) {
      values.remove(ind)
      localVars.remove(ind - globalVars.size)
    }

    private def outputClause : Unit = outputClause(newPred(Nil, None).pred)
    private def outputClause(ccPred : CCPredicate) : Unit =
      outputClause(ccPred.pred)

    def genClause(pred : Predicate) : Clause = {
      import HornClauses._
      if (initAtom == null)
        throw new TranslationException("too complicated initialiser")
      asAtom(pred) :- (initAtom &&& guard)
    }

    def outputClause(pred : Predicate,
                     sync : ParametricEncoder.Synchronisation =
                       ParametricEncoder.NoSync) : Unit = {
      if(!noSideEffects) {
        val c = genClause(pred)
        if (!c.hasUnsatConstraint)
          output(c, sync)
        resetFields(pred)
      }
    }

    def outputClause(headAtom : IAtom) : Unit = {
      import HornClauses._
      val c = headAtom :- (initAtom &&& guard)
      if (!c.hasUnsatConstraint)
        output(c)
    }

    def resetFields(pred : Predicate) : Unit = {
      initAtom = atom(pred, allFormalVarTerms)
      guard = true
      touchedGlobalState = false
      assignedToStruct = false
      for ((e, i) <- allFormalExprs.iterator.zipWithIndex)
        values(i) = e
    }

    def outputITEClauses(cond : IFormula,
                         thenPred : Predicate, elsePred : Predicate) = {
      saveState
      addGuard(cond)
      outputClause(thenPred)
      restoreState
      addGuard(~cond)
      outputClause(elsePred)
    }

    def assertProperty(property : IFormula,
                       srcInfo : Option[SourceInfo]) : Unit = {
      import HornClauses._
      assertionClauses += CCClause((property :- (initAtom &&& guard)), srcInfo)
    }

    def addValue(t : CCExpr) = {
      values += t
      touchedGlobalState = touchedGlobalState || !freeFromGlobal(t)
    }

    private def getValue(name : String,
                         isIndirection : Boolean = false) : CCExpr =
      getValue(lookupVar(name), isIndirection)
    private def getValue(ind : Int,
                         isIndirection : Boolean) : CCExpr =
      if (isIndirection)
        getPointedTerm(getPointerType(ind))
      else
        values(ind)

    private def getPointedTerm (ptrType : CCStackPointer) =
      ptrType.fieldAddress match {
        case Nil => getValue(ptrType.targetInd, false)
        case _ =>
          val structVal = getValue(ptrType.targetInd, false)
          val structType = structVal.typ.asInstanceOf[CCStruct]
          CCTerm(
            structType.getFieldTerm(structVal.toTerm, ptrType.fieldAddress),
            structType.getFieldType(ptrType.fieldAddress), None) // todo: src Info?
      }

    private def setValue(name : String, t : CCExpr,
                         isIndirection : Boolean = false) : Unit =
      setValue(lookupVar(name), t, isIndirection)
    private def setValue(ind: Int, t : CCExpr,
                         isIndirection : Boolean) : Unit = {
      if (!noSideEffects) {
        val actualInd = getValue(ind, false).typ match {
          case stackPtr: CCStackPointer => stackPtr.targetInd
          case _ => ind
        }
        values(actualInd) = t
        /* if(isIndirection) {
          //val ptrType = getPointerType(ind)
          getValue(ind, false).typ match {
            case stackPtr : CCStackPointer =>
              val actualInd = getActualInd(ind)
              values(actualInd) = t/* stackPtr.fieldAddress match {
                case Nil => t
                case _ =>
                  val pointedStruct = values(stackPtr.targetInd)
                  val structType = pointedStruct.typ.asInstanceOf[CCStruct]
                  CCTerm(
                    structType.setFieldTerm(
                      pointedStruct.toTerm, t.toTerm, stackPtr.fieldAddress),
                    structType)
              }*/
              actualInd
            case _ => throw new TranslationException(
              "Trying to use a non-pointer as a pointer!")
          }
        }
        else {
          values(ind) = t
          ind
        }*/
        touchedGlobalState =
          touchedGlobalState || actualInd < globalVars.size || !freeFromGlobal(t)
      }
    }

    private def getVar (ind : Int) : CCVar = {
      if (ind < globalVars.size) globalVars.vars(ind)
      else localVars.vars(ind - globalVars.size)
    }
    private def getVar (name : String) : CCVar = {
      val ind = lookupVar(name)
      getVar(ind)
    }

    // goes bottom-up from a given field, and pushes parent types to the stack.
    // the top parent is at the bottom of the stack.
    private def getParentTypes(exp: Exp) : Stack[CCStruct] = {
      val typeStack = new Stack[CCStruct]
      fillParentTypes(exp.asInstanceOf[Eselect].exp_) //fills a stack bottom-up
      def fillParentTypes(expField: Exp) : CCType = {
        val thisType = expField match {
          case nested: Eselect => {
            val parentType = fillParentTypes(nested.exp_).asInstanceOf[CCStruct]
            parentType.getFieldType(parentType.getFieldIndex(nested.cident_))
          }
          case variable: Evar =>
            getVar(variable.cident_).typ.asInstanceOf[CCStruct]
        }
        if(thisType.isInstanceOf[CCStruct])
          typeStack.push(thisType.asInstanceOf[CCStruct])
        thisType
      }
      typeStack
    }

    def getValues : Seq[CCExpr] =
      values.toList
    def getValuesAsTerms : Seq[ITerm] =
      for (expr <- values.toList) yield expr.toTerm

    def asAtom(pred : Predicate) = atom(pred, getValuesAsTerms)

    def asLValue(exp : Exp) : String = exp match {
      case exp : Evar    => exp.cident_
      case exp : Eselect => asLValue(exp.exp_)
      case exp : Epoint  => asLValue(exp.exp_)
      case exp : Epreop  => asLValue(exp.exp_)
      case exp : Eassign => asLValue(exp.exp_1)
      case exp : Earray  => asLValue(exp.exp_1)
      case exp =>
        throw new TranslationException(
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isClockVariable(exp : Exp) : Boolean = exp match {
      case exp : Evar => getValue(exp.cident_).typ.isInstanceOf[CCClock]
      case _ : Eselect | _ : Epreop | _ : Epoint | _ : Earray => false
      case exp =>
        throw new TranslationException(getLineString(exp) +
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isDurationVariable(exp : Exp) : Boolean = exp match {
      case exp : Evar => getValue(exp.cident_).typ.isInstanceOf[CCDuration]
      case _ : Eselect | _ : Epreop | _ : Epoint | _ : Earray => false
      case exp =>
        throw new TranslationException(getLineString(exp) +
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isHeapRead(t : CCExpr) =
      t.toTerm match {
        case IFunApp(f, _) if objectGetters contains f => true
        case _ => false
      }
      /*t.toTerm.isInstanceOf[IFunApp] &&
        t.toTerm.asInstanceOf[IFunApp] match {
          case Left(c) => c.sort.isInstanceOf[Heap.HeapSort]
          case Right(f) => objectGetters contains f.fun
        }*/
    private def isHeapStructFieldRead (t : CCExpr) =
      t.toTerm match {
        case f : IFunApp => getFieldInfo(f)._2.isRight
        case _ => false
      }

    private def isHeapPointer(t : CCExpr) =
      t.typ match {
        case _ : CCHeapPointer      => true
        case _ : CCHeapArrayPointer => true
        case _                      => false
      }
    private def isHeapPointer(exp : Exp) =
      getVar(asLValue(exp)).typ match {
        case _ : CCHeapPointer      => true
        case _ : CCHeapArrayPointer => true
        case _                      => false
      }

    private def isIndirection(exp : Exp) : Boolean =
      exp match {
        case exp : Epreop => exp.unary_operator_.isInstanceOf[Indirection]
        case _ => false
      }

    private def getPointerType(ind : Int) = {
      getValue(ind, false).typ match {
        case ptrType : CCStackPointer => ptrType
        case _ => throw new TranslationException(
          "Trying to use non-pointer as a pointer!")
      }
    }

    private def getActualInd(ind : Int) : Int =
      values(ind).typ match {
        case pTyp : CCStackPointer => pTyp.targetInd
        case _ => throw new TranslationException("Trying to dereference " +
          "a non-pointer!")
      }

    var evaluatingLhs = false
    var handlingFunContractArgs = false
    var lhsIsArrayPointer = false
    def evalLhs(exp : Exp) : CCExpr = {
      evaluatingLhs = true
      val res = eval(exp)
      evaluatingLhs = false
      res
    }

    def eval(exp : Exp) : CCExpr = {
      val initSize = values.size
      evalHelp(exp)
      val res = popVal
      assert(initSize == values.size)
      res
    }

    def evalList(exp : Exp) : Seq[CCExpr] = {
      val res = new ArrayBuffer[CCExpr]

      var e = exp
      while (e.isInstanceOf[Ecomma]) {
        val ec = e.asInstanceOf[Ecomma]
        res += eval(ec.exp_2)
        e = ec.exp_1
      }

      res += eval(e)

      res.toList
    }

    def atomicEval(exp : Exp) : CCExpr = atomicEval(List(exp))

    def atomicEval(exps : Seq[Exp]) : CCExpr = {
      val currentClauseNum = clauses.size
      val initSize = values.size

      inAtomicMode {
        pushVal(CCFormula(true, CCVoid(), None))
        for (exp <- exps) {
          popVal
          evalHelp(exp)
        }
      }

      if (currentClauseNum != clauses.size) {
        outputClause
        mergeClauses(currentClauseNum)
      }
      val res = popVal
      assert(initSize == values.size)
      res
    }

    // This function returns the actual term after an assignment is done.
    // E.g. for non ADT lhs, this is the same as the rhs,
    //      for ADT lhs, this is the lhs updated with the value of rhs.
    private def getActualAssignedTerm(lhs: CCExpr, rhs: CCExpr) = {
      if (rhs.typ.isInstanceOf[CCStruct] && (rhs.typ != lhs.typ))
        throw new TranslationException("Cannot assign " + rhs.typ +
          " to " + lhs.typ + "!")

        lhs.toTerm match {
        case fieldFun : IFunApp => // an ADT
          assignedToStruct = true
          val (fieldNames, rootTerm) = getFieldInfo(fieldFun)

          rootTerm match {
            case Left(t) =>
              val structType = structDefs(t.sort.name)
              val fieldAddress = structType.getFieldAddress(fieldNames)
              CCTerm(structType.setFieldTerm(t, rhs.toTerm, fieldAddress),
                structType, rhs.srcInfo)
            case Right(f) =>
              val structType =
                structDefs(f.fun.asInstanceOf[MonoSortedIFunction].resSort.name)
              val fieldAddress = structType.getFieldAddress(fieldNames)
              CCTerm(structType.setFieldTerm(f, rhs.toTerm, fieldAddress),
                structType, rhs.srcInfo)
            /*case _ => {getVarType(rootTerm.name) match {
                case ptr : CCStackPointer => getPointedTerm(ptr).typ
                case typ => typ
              }}.asInstanceOf[CCStruct]*/
          }
        case _ => rhs // a non ADT
      }
    }

    // Returns the root term and a list of names pointing to the given field.
    // todo: this works incorrectly when root is not a pointer but the field is
    // e.g. getInt(read(h, f(someStruct)))
    private def getFieldInfo(nested : IFunApp) :
    (List[String], Either[SortedConstantTerm, IFunApp]) = {
      val fieldNames = List()
      getFieldInfo(nested, fieldNames)
    }
    private def getFieldInfo(nested : IFunApp, fieldNames : List[String])
    : (List[String], Either[SortedConstantTerm, IFunApp]) = {
      nested.args.size match {
        case n if n > 1 => (fieldNames, Left(getStructTerm(nested)))
        case n if n == 1 =>
          nested.args.head match{
            case nestedMore : IFunApp if !(objectGetters contains nestedMore.fun) =>
              getFieldInfo(nestedMore, nested.fun.name :: fieldNames)
            case objectGetter : IFunApp =>
              (nested.fun.name :: fieldNames, Right(objectGetter))
            case lastLevel : IConstant =>
              (nested.fun.name :: fieldNames,
                Left(lastLevel.c.asInstanceOf[SortedConstantTerm]))
          }
        case _ => throw new TranslationException("Cannot get field names " +
          "from given struct term " + nested)
      }
    }
    private def getStructTerm(nested : ITerm) : SortedConstantTerm = { // todo
      nested match {
        case nestedMore : IFunApp => getStructTerm(nestedMore.args.head)
        case lastLevel : IConstant => lastLevel.c.asInstanceOf[SortedConstantTerm]
        case _ => throw new TranslationException(nested + " is not a struct.")
      }
    }

    private def evalHelp(exp : Exp) : Unit = exp match {
      case exp : Ecomma => {
        evalHelp(exp.exp_1)
        popVal
        maybeOutputClause
        evalHelp(exp.exp_2)
      }
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign] &&
                             isClockVariable(exp.exp_1)) => {
        evalHelp(exp.exp_2)
        maybeOutputClause
        setValue(asLValue(exp.exp_1), translateClockValue(topVal))
      }
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign] &&
                             isDurationVariable(exp.exp_1)) => {
        evalHelp(exp.exp_2)
        maybeOutputClause
        setValue(asLValue(exp.exp_1), translateDurationValue(topVal))
      }
      case exp : Eassign if exp.assignment_op_.isInstanceOf[Assign] => {
        // if lhs is array pointer, an alloc rhs evaluation should produce an
        // AddressRange even if the allocation size is only 1.
        evalHelp(exp.exp_2) //first evaluate rhs and push
        maybeOutputClause
        val rhsVal = popVal
        val lhsVal = eval(exp.exp_1) //then evaluate lhs and get it
        val updatingPointedValue =
          isHeapRead(lhsVal) || // *(p) = ... where p is a heap ptr
          isHeapStructFieldRead(lhsVal) // ps->f = ... where ps is a heap ptr
        val lhsIsArraySelect =
          lhsVal.toTerm match {
            case IFunApp(ExtArray.Select(_), _) => true
            case _ => false
          }
        if(lhsIsArrayPointer || isHeapPointer(lhsVal) || updatingPointedValue ||
          lhsIsArraySelect) {
          if (updatingPointedValue)
            heapWrite(lhsVal.toTerm.asInstanceOf[IFunApp], rhsVal, true, true)
          else if (lhsIsArraySelect) { // todo: this branch needs to be rewritten, it was hastily coded to deal with arrays inside structs.
            val newTerm = CCTerm(
              writeADT(lhsVal.toTerm.asInstanceOf[IFunApp],
                         rhsVal.toTerm, heap.userADTCtors, heap.userADTSels),
                       lhsVal.typ, rhsVal.srcInfo)
            val lhsName = asLValue(exp.exp_1)
            val oldLhsVal = getValue(lhsName)
            val innerTerm = lhsVal.toTerm.asInstanceOf[IFunApp].args.head
            val actualLhsTerm = getActualAssignedTerm(
              CCTerm(innerTerm, oldLhsVal.typ, rhsVal.srcInfo), newTerm)
            setValue(asLValue(exp.exp_1), actualLhsTerm)
          } else {
            val lhsName = asLValue(exp.exp_1)
            val actualRhsVal = rhsVal.toTerm match {
              case lit : IIntLit =>
                if (lit.value.intValue != 0) {
                  throw new TranslationException("Pointer arithmetic is not " +
                    "allowed, and the only assignable integer value for " +
                    "pointers is 0 (NULL)")
                } else CCTerm(heap.nullAddr(), CCHeapPointer(heap, lhsVal.typ), rhsVal.srcInfo)
              case _ => rhsVal
            }
            val actualLhsTerm = getActualAssignedTerm(lhsVal, actualRhsVal)
            rhsVal.typ match {
              case arrayPtr1 : CCHeapArrayPointer =>
                lhsVal.typ match {
                  case _ : CCHeapPointer =>
                    throw new TranslationException(getLineString(exp) +
                      "Cannot assign an array value to " + lhsName + ". " +
                      "Declaring " + lhsName + " as " + lhsName + "[] might " +
                      "solve this issue.")
                  case arrayPtr2 : CCHeapArrayPointer =>
                    if (arrayPtr1 != arrayPtr2) {
                      if (arrayPtr1.arrayLocation == StackArray &&
                          arrayPtr2.arrayLocation == HeapArray) // -> alloca
                        updateVarType(lhsName, arrayPtr1) // todo: replace with a static analysis? we should detect arrays on stack beforehand maybe?
                      else throw new TranslationException(getLineString(exp) +
                        "Unsupported operation: pointer " + lhsName +
                        " points to elements of multiple arrays (or array types)." +
                        "Try initialising the array directly.")
                    }
                  case _ => // nothing
                }
              case _ => // nothing
            }
            setValue(lhsName, actualLhsTerm)
          }
        } else {
          val lhsName = asLValue(exp.exp_1)
          val actualLhsTerm = getActualAssignedTerm(lhsVal, rhsVal)
          setValue(lhsName, actualLhsTerm)
        }
        pushVal(rhsVal)
      }
      case exp : Eassign => {
        evalHelp(exp.exp_1)
        val lhsVal = topVal
        maybeOutputClause
        evalHelp(exp.exp_2)
        maybeOutputClause
        val rhsE = popVal
        val rhs = rhsE.toTerm
        val lhsE = popVal
        val lhs = lhsE.toTerm
        if (lhsE.typ.isInstanceOf[CCClock] || lhsE.typ.isInstanceOf[CCDuration])
          throw new TranslationException("unsupported assignment to clock")
        val newVal = CCTerm(lhsE.typ cast (exp.assignment_op_ match {
          case _ : AssignMul =>
            ap.theories.nia.GroebnerMultiplication.mult(lhs, rhs)
          case _ : AssignDiv =>
            ap.theories.nia.GroebnerMultiplication.tDiv(lhs, rhs)
          case _ : AssignMod =>
            ap.theories.nia.GroebnerMultiplication.tMod(lhs, rhs)
          case _ : AssignAdd =>
            (lhsE.typ, rhsE.typ) match {
              case (_ : CCHeapArrayPointer, _ : CCArithType) =>
                addToAddressRangeStart(lhs, rhs)
              case _ => lhs + rhs
            }
          case _ : AssignSub =>
            (lhsE.typ, rhsE.typ) match {
              case (arrType : CCHeapArrayPointer, _ : CCArithType) =>
                throw new TranslationException("Only addition is allowed in " +
                  "array pointer arithmetic.") // due to how AddressRange is defined: <startAddr, size>
                //addToAddressRangeStart(lhsE, rhsE, arrType, _ - _).toTerm
              case _ => lhs - rhs
            }
          case _ : AssignLeft =>
            ModuloArithmetic.bvshl(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignRight =>
            ModuloArithmetic.bvashr(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignAnd =>
            ModuloArithmetic.bvand(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignXor =>
            ModuloArithmetic.bvxor(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
          case _ : AssignOr =>
            ModuloArithmetic.bvand(lhsE.typ cast2Unsigned lhs,
              lhsE.typ cast2Unsigned rhs)
        }), lhsE.typ, lhsE.srcInfo)
        pushVal(newVal)

        val updatingPointedValue =
          isHeapRead(lhsVal) || // *(p) = ... where p is a heap ptr
            isHeapStructFieldRead(lhsVal) // ps->f = ... where ps is a heap ptr

        if(isHeapPointer(exp) && updatingPointedValue) {
          heapWrite(lhsVal.toTerm.asInstanceOf[IFunApp], newVal, true, true)
        } else {
          setValue(lookupVar(asLValue(exp.exp_1)),
            getActualAssignedTerm(lhsVal, newVal),
            isIndirection(exp.exp_1)) // todo get rid of indirections?
        }
      }
      case exp : Econdition => {
        val cond = eval(exp.exp_1).toFormula

        saveState
        addGuard(cond)
        evalHelp(exp.exp_2)
        outputClause
        val intermediatePred = initPred

        restoreState
        addGuard(~cond)
        evalHelp(exp.exp_3)
        outputClause(intermediatePred)
      }
      case exp : Elor => {
        evalHelp(exp.exp_1)
        maybeOutputClause
        val cond = popVal.toFormula

        saveState
        addGuard(~cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond ||| cond2, CCInt(),
            Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))))
        } else {
          outputClause
          val intermediatePred = initPred

          restoreState
          addGuard(cond)
          pushVal(CCFormula(true, CCInt(),
            Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))))
          outputClause(intermediatePred)
        }
      }
      case exp : Eland => {
        evalHelp(exp.exp_1)
        maybeOutputClause
        val cond = popVal.toFormula

        saveState
        addGuard(cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond &&& cond2, CCInt(),
            Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))))
        } else {
          outputClause
          val intermediatePred = initPred

          restoreState
          addGuard(~cond)
          pushVal(CCFormula(false, CCInt(),
            Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))))
          outputClause(intermediatePred)
        }
      }
      case exp : Ebitor =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvor(_, _))
      case exp : Ebitexor =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvxor(_, _))
      case exp : Ebitand =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvand(_, _))
      case exp : Eeq =>
        strictBinPred(exp.exp_1, exp.exp_2, _ === _)
      case exp : Eneq =>
        strictBinPred(exp.exp_1, exp.exp_2, _ =/= _)
      case exp : Elthen =>
        strictBinPred(exp.exp_1, exp.exp_2, _ < _)
      case exp : Egrthen =>
        strictBinPred(exp.exp_1, exp.exp_2, _ > _)
      case exp : Ele =>
        strictBinPred(exp.exp_1, exp.exp_2, _ <= _)
      case exp : Ege =>
        strictBinPred(exp.exp_1, exp.exp_2, _ >= _)
      case exp : Eleft =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvshl(_, _))
      case exp : Eright =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvashr(_, _))
      case exp : Eplus =>
        strictBinFun(exp.exp_1, exp.exp_2, _ + _, opIsAddition = true)
      case exp : Eminus =>
        strictBinFun(exp.exp_1, exp.exp_2, _ - _)
      case exp : Etimes =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.nia.GroebnerMultiplication.mult(x, y)
        })
      case exp : Ediv =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.nia.GroebnerMultiplication.tDiv(x, y)
        })
      case exp : Emod =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.nia.GroebnerMultiplication.tMod(x, y)
        })
      case exp : Etypeconv => {
        evalHelp(exp.exp_)
        pushVal(convertType(popVal, getType(exp.type_name_)))
      }
      case _ : Epreinc | _ : Epredec =>
        val (preExp, op) = exp match {
          case exp : Epreinc => (exp.exp_, +1)
          case exp : Epredec => (exp.exp_, -1)
        }
        evalHelp(preExp)
        val lhsVal = topVal // todo : check if necessary, maybe just use topVal?
        maybeOutputClause
        pushVal(popVal mapTerm (_ + op))
        if(isHeapPointer(preExp)) {
          heapWrite(lhsVal.toTerm.asInstanceOf[IFunApp], topVal, true, true)
        } else {
          setValue(lookupVar(asLValue(preExp)),
            getActualAssignedTerm(lhsVal, topVal),
            isIndirection(preExp)) // todo get rid of indirection?
        }
      case exp : Epreop => {
        val srcInfo = Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))
        evalHelp(exp.exp_)
        exp.unary_operator_ match {
          case _ : Address    =>
            topVal.toTerm match {
              case fieldFun: IFunApp
                if !(objectGetters contains fieldFun.fun) &&
                   (heap.userADTSels exists(_ contains fieldFun.fun)) => // an ADT
                val (fieldNames, rootTerm) = getFieldInfo(fieldFun)
                rootTerm match {
                  case Left(c) =>
                    val rootInd: Int = lookupVar(c.name)
                    val structType = getValue(rootInd, false).typ.asInstanceOf[CCStruct]
                    assert(rootInd > -1 && rootInd < values.size - 1) // todo
                    val ptr = CCStackPointer(rootInd, popVal.typ, structType.getFieldAddress(fieldNames))
                    pushVal(CCTerm(IExpression.Int2ITerm(rootInd), ptr, srcInfo)) //we don't care about the value
                  case Right(c) =>
                    // newAddr(alloc(h, WrappedAddr(getPtrField(getStruct(read(h, p))))))
                    // here topVal = getPtrField(getStruct(read(h, p))), we construct the rest
                    // this is to allocate memory for expressions like:
                    // &((*p)->tail)
                    // alternatively one could rewrite this using a temporary variable
                    // and create a stack pointer to it (but this needs to be done during preprocessing,
                    //otherwise when we evaluate this we would be pushing two terms instead of one)
                    val newTerm = heapAlloc(popVal.asInstanceOf[CCTerm])
                    maybeOutputClause
                    assert(c.args.size == 1)
                    val readObj = c.args.head
                    val resSort = c.fun.asInstanceOf[MonoSortedIFunction].resSort
                    addGuard(heap.heapADTs.hasCtor(readObj, sortCtorIdMap(resSort)))
                    pushVal(newTerm)
                }
              case f : IFunApp if objectGetters contains f.fun => // a heap read (might also be from a heap array)
                val readFunApp = f.args.head.asInstanceOf[IFunApp] // sth like read(h, ...)
                val Seq(heapTerm, addrTerm) = readFunApp.args
                // todo: below type extraction is not safe!
                val t = addrTerm match {
                  case IFunApp(heap.nth, args) => // if nthAddrRange(a, i)
                    val Seq(arrTerm, indTerm) = args
                    // return the addressRange starting from i
                    CCTerm(addToAddressRangeStart(arrTerm, indTerm),
                      getValue(arrTerm.asInstanceOf[IConstant].c.name).typ, srcInfo
                    )
                  case _ =>
                    CCTerm(addrTerm, CCHeapPointer(heap,
                      getValue(addrTerm.asInstanceOf[IConstant].c.name).typ), srcInfo)
                }
                popVal
                pushVal(t)

              case _ =>
                val t = if (handlingFunContractArgs) {
                  val newTerm = heapAlloc(popVal.asInstanceOf[CCTerm])
                  maybeOutputClause
                  newTerm
                } else {
                  val ind = values.indexWhere(v => v == topVal)
                  assert(ind > -1 && ind < values.size - 1) // todo
                  val ptr = CCStackPointer(ind, popVal.typ, Nil)
                  CCTerm(IExpression.Int2ITerm(ind), ptr, srcInfo)
                }
                pushVal(t) //we don't care about the value
            }
          case _ : Indirection =>
            val v = popVal
            v.typ match { // todo: type checking?
              case ptr : CCStackPointer => pushVal(getPointedTerm(ptr))
              case   _ : CCHeapPointer =>
                if(evaluatingLhs) pushVal(v)
                else pushVal(heapRead(v))
              case  arr : CCHeapArrayPointer =>
                if(evaluatingLhs) pushVal(v)
                else pushVal(heapArrayRead(v, CCTerm(IIntLit(0), CCInt(), srcInfo), arr))
              case _ => throw new TranslationException("Cannot dereference " +
                  "non-pointer: " + v.typ + " " + v.toTerm)
            }
          case _ : Plus       => // nothing
          case _ : Negative   =>
            val t = popVal mapTerm (-(_))
            pushVal(CCTerm(t.toTerm, t.typ, srcInfo))
//          case _ : Complement.  Unary_operator ::= "~" ;
          case _ : Logicalneg =>
            pushVal(CCFormula(~popVal.toFormula, CCInt(), srcInfo))
        }
      }
//      case exp : Ebytesexpr.  Exp15 ::= "sizeof" Exp15;
//      case exp : Ebytestype.  Exp15 ::= "sizeof" "(" Type_name ")";
//      case exp : Earray.      Exp16 ::= Exp16 "[" Exp "]" ;

      case exp : Efunk => {
        val srcInfo = Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))
        // inline the called function
        printer print exp.exp_ match {
          case "__VERIFIER_error" | "reach_error" => {
            assertProperty(false, srcInfo)
            pushVal(CCFormula(true, CCInt(), srcInfo))
          }
          case name => {
            outputClause
            handleFunction(name, initPred, 0)
          }
        }
      }

      case exp : Efunkpar =>
        val srcInfo = Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))
        (printer print exp.exp_) match {
          case "assert" | "static_assert" | "__VERIFIER_assert"
                          if (exp.listexp_.size == 1) => {
            withoutSideEffects(eval(exp.listexp_.head)) match {
              case f@CCFormula(IAtom(_, _), _, srcInfo) =>
                // todo: why atomicEval fails for uninterpreted predicate hints?
                assertProperty(eval(exp.listexp_.head).toFormula, srcInfo)
              case f =>
                assertProperty(atomicEval(exp.listexp_.head).toFormula, srcInfo)
            }
            pushVal(CCFormula(true, CCInt(), srcInfo))
          }
        case "assume" | "__VERIFIER_assume"
                          if (exp.listexp_.size == 1) => {
            withoutSideEffects(eval(exp.listexp_.head)) match {
              case f@CCFormula(IAtom(_, _), _, _) =>
                // todo: why atomicEval fails for uninterpreted predicate hints?
                addGuard(eval(exp.listexp_.head).toFormula)
              case f =>
                addGuard(atomicEval(exp.listexp_.head).toFormula)
            }
            pushVal(CCFormula(true, CCInt(), srcInfo))
        }
        case cmd@("chan_send" | "chan_receive") if (exp.listexp_.size == 1) => {
          val name = printer print exp.listexp_.head
          (channels get name) match {
            case Some(chan) => {
              val sync = cmd match {
                case "chan_send"    => ParametricEncoder.Send(chan)
                case "chan_receive" => ParametricEncoder.Receive(chan)
              }
              outputClause(newPred(Nil, None).pred, sync)
              pushVal(CCFormula(true, CCInt(), srcInfo))
            }
            case None =>
              throw new TranslationException(
                name + " is not a declared channel")
          }
        }
        case name@("malloc" | "calloc" | "alloca" | "__builtin_alloca")
          if !TriCeraParameters.parameters.value.useArraysForHeap => { // todo: proper alloca and calloc
          if (!modelHeap)
            throw NeedsHeapModelException
          val (typ, allocSize) = exp.listexp_(0) match {
            case exp : Ebytestype =>
              (getType(exp), CCTerm(IIntLit(IdealInt(1)), CCInt(), srcInfo))
            //case exp : Ebytesexpr => eval(exp.exp_).typ - handled by preprocessor
            case exp : Etimes =>
              exp.exp_1 match {
                case e : Ebytestype =>
                  (getType(e), eval(exp.exp_2))
                case e if exp.exp_2.isInstanceOf[Ebytestype] =>
                  (getType(exp.exp_2.asInstanceOf[Ebytestype]), eval(e))
                case _ =>
                  throw new TranslationException(
                    "Unsupported alloc expression: " + (printer print exp))
              }
            //case exp : Evar => // allocation in bytes

            case _ => throw new TranslationException(
              "Unsupported alloc expression: " + (printer print exp))
          }

          val arrayType = name match {
            case "malloc" | "calloc"           => HeapArray
            case "alloca" | "__builtin_alloca" => StackArray
          }
          val objectTerm = CCTerm(name match {
            case "calloc"                                 => typ.getZeroInit
            case "malloc" | "alloca" | "__builtin_alloca" => typ.getNonDet
          }, typ, srcInfo)

          allocSize match {
            case CCTerm(IIntLit(IdealInt(1)), typ, srcInfo)
              if typ.isInstanceOf[CCArithType] && !lhsIsArrayPointer =>
              pushVal(heapAlloc(objectTerm))
            case CCTerm(sizeExp, typ, srcInfo) if typ.isInstanceOf[CCArithType] =>
              val addressRangeValue = heapBatchAlloc(objectTerm, sizeExp)
//              localVars.incrementLastFrame
              // todo: values addGuard ?
              pushVal(CCTerm(addressRangeValue, CCHeapArrayPointer(heap, typ, arrayType), srcInfo))
            // case CCTerm(IIntLit(IdealInt(n)), CCInt) =>
                // todo: optimise constant size allocations > 1?
          }
        }
        case name@("malloc" | "calloc" | "alloca" | "__builtin_alloca")
          if TriCeraParameters.parameters.value.useArraysForHeap => {
          val (typ, allocSize) = exp.listexp_(0) match {
            case exp : Ebytestype =>
              (getType(exp), CCTerm(IIntLit(IdealInt(1)), CCInt(), srcInfo))
            //case exp : Ebytesexpr => eval(exp.exp_).typ - handled by preprocessor
            case exp : Etimes =>
              exp.exp_1 match {
                case e : Ebytestype =>
                  (getType(e), eval(exp.exp_2))
                case e if exp.exp_2.isInstanceOf[Ebytestype] =>
                  (getType(exp.exp_2.asInstanceOf[Ebytestype]), eval(e))
                case _ =>
                  throw new TranslationException(
                    "Unsupported alloc expression: " + (printer print exp))
              }
            //case exp : Evar => // allocation in bytes

            case _ => throw new TranslationException(
              "Unsupported alloc expression: " + (printer print exp))
          }

          val (sizeExpr, sizeInt) = allocSize match {
            case CCTerm(IIntLit(IdealInt(n)), typ, srcInfo)
              if typ.isInstanceOf[CCArithType] && !lhsIsArrayPointer =>
              (Some(allocSize), Some(n))
            case _ =>
              (Some(allocSize), None)
          }
          val arrayLocation = name match {
            case "malloc" | "calloc"           => HeapArray
            case "alloca" | "__builtin_alloca" => StackArray
          }

          val theory = ExtArray(Seq(CCInt().toSort), typ.toSort) // todo: only 1-d int arrays...
          val arrType = CCArray(typ, sizeExpr, sizeInt, theory, arrayLocation)

          val arrayTerm = CCTerm(name match {
            case "calloc"                                 => arrType.getZeroInit
            case "malloc" | "alloca" | "__builtin_alloca" => arrType.getNonDet
          }, arrType, srcInfo)

          pushVal(arrayTerm)
        }
        case "realloc" =>
          if (!modelHeap)
            throw NeedsHeapModelException
          throw new TranslationException("realloc is not supported.")
        case "free" => // todo: what about trying to free unallocated or already freed addresses?
          if (!modelHeap)
            throw NeedsHeapModelException
          val t = atomicEval(exp.listexp_.head)
          heapFree(t)
          pushVal(CCTerm(0, CCVoid(), srcInfo)) // free returns no value, pushing dummy
        case fun@("\\sum" | "\\max" | "\\min" | "\\numof" | "\\product") =>
          // \sum(a, lo, hi)
          // todo: naive fragile implementation without any checks
          val arrayTerm = eval(exp.listexp_(0)) // todo: make the order the same as in ACSL? e.g., \max(lo, hi, a)
          val loTerm = eval(exp.listexp_(1))
          val hiTerm = eval(exp.listexp_(2))
          val f: (ITerm, ITerm) => ITerm =
            (a : ITerm, b : ITerm) => fun match {
            case "\\sum" => a + b
            case "\\max" => IExpression.ite(a >= b, a, b)
            case "\\min" => IExpression.ite(a <= b, a, b)
            case "\\numof" => ???
            case "\\product" =>
              ap.theories.nia.GroebnerMultiplication.multSimplify(a, b)
          }
          val fInv: Option[(ITerm, ITerm) => ITerm] = fun match {
            case "\\sum" => Some((a : ITerm, b : ITerm) => a - b)
            case "\\max" => None
            case "\\min" => None
            case "\\numof" => Some(???)
            case "\\product" => None
          }

          val arrayType = arrayTerm.typ.asInstanceOf[CCArray]

          val identity: ITerm = fun match {
            case "\\sum" => IExpression.i(0)
            case "\\max" =>
              arrayType.elementType.range._1 match {
                case Some(v) => v
                case None =>
                  val v = IdealInt("-9223372036854775808")
                  warn(s"Using $v for empty ranges for \\max.")
                  IExpression.i(v)
              }
            case "\\min" =>
              arrayType.elementType.range._2 match {
                case Some(v) => v
                case None =>
                  val v = IdealInt("9223372036854775807")
                  warn(s"Using $v for empty ranges for \\min.")
                  IExpression.i(v)
              }
            case "\\numof" => ???
            case "\\product" => IExpression.i(1)
          }


          val extQuan = new ExtendedQuantifier(fun, arrayType.arrayTheory,
            identity, f, fInv, None, None, None)

          ap.theories.TheoryRegistry.register(extQuan) // todo: can we avoid this?

          pushVal(CCTerm(extQuan.fun(
            arrayTerm.toTerm, loTerm.toTerm, hiTerm.toTerm),
            arrayType.elementType, srcInfo))

        case name => {
          // then we inline the called function

          // evaluate the arguments
          // todo: if we are to handle a function contract, arguments are handled
          // as heap pointers. if the function is to be inlined, then arguments
          // are handled as stack pointers. here we set a flag to notify this
          handlingFunContractArgs = functionContexts.contains(name)
          for (e <- exp.listexp_)
            evalHelp(e)
          if(!handlingFunContractArgs) outputClause
          handlingFunContractArgs = false

          val functionEntry = initPred

          handleFunction(name, functionEntry, exp.listexp_.size)
        }
      }

      case exp : Eselect => {
        val srcInfo = Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))
        val evaluatingLhs_pre = evaluatingLhs
        evaluatingLhs = false
        val subexpr = eval(exp.exp_)
        evaluatingLhs = evaluatingLhs_pre
        val fieldName = exp.cident_
        subexpr.typ match {
          case structType : CCStruct => { // todo a better way
            if(!structType.contains(fieldName))
              throw new TranslationException(fieldName + " is not a member of "
                + structType + "!")
            val ind = structType.getFieldIndex(fieldName)
            val fieldType = structType.getFieldType(ind) /*match {
              case declPtr : CCDeclarationOnlyPointer if !evaluatingLhs =>
                getHeapPointer (declPtr)
              case typ => typ
            }*/
            val sel = structType.getADTSelector(ind)
            pushVal(CCTerm(sel(subexpr.toTerm), fieldType, srcInfo))
          }
          case _ =>
            throw new TranslationException("Trying to access field '." +
              fieldName + "' of a variable which is not a struct.")
        }
      }

      case exp : Epoint => {
        val srcInfo = Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))
        val evaluatingLhs_pre = evaluatingLhs
        evaluatingLhs = false
        val subexpr = eval(exp.exp_)
        evaluatingLhs = evaluatingLhs_pre
        val fieldName = exp.cident_
        val term = subexpr.typ match {
          case ptrType : CCStackPointer => getPointedTerm(ptrType)
          case _ : CCHeapPointer =>  //todo: error here if field is null
            heapRead(subexpr)
          case _ => throw new TranslationException(
            "Trying to access field '->" + fieldName + "' of non pointer.")
        }
        val structType = term.typ match {
          case typ : CCStruct => typ
          case CCStructField(name, structs) => structs(name)
          case typ => throw new TranslationException("Epoint is currently " +
            "only implemented for structs, not " + typ + ": " +
            (printer print exp))
        }
        if(!structType.contains(fieldName))
          throw new TranslationException(fieldName + " is not a member of "
            + structType + "!")
        val ind = structType.getFieldIndex(fieldName)
        val fieldType = structType.getFieldType(ind)
        val sel = structType.getADTSelector(ind)
        pushVal(CCTerm(sel(term.toTerm), fieldType, srcInfo))
      }

      case _ : Epostinc | _ : Epostdec=>
        val (postExp, op) = exp match {
          case exp : Epostinc => (exp.exp_, +1)
          case exp : Epostdec => (exp.exp_, -1)
        }
        evalHelp(postExp)
        val evalExp = topVal
        maybeOutputClause
        if(isHeapPointer(postExp)) {
          heapWrite(evalExp.toTerm.asInstanceOf[IFunApp], topVal.mapTerm(_ + op),
            assertMemSafety = true,
            assumeMemSafety = true)
        } else {
          setValue(lookupVar(asLValue(postExp)),
            getActualAssignedTerm(evalExp, topVal.mapTerm(_ + op)),
            isIndirection(postExp)) // todo get rid of indirection?
        }

      case exp : Evar => {
        val name = exp.cident_
        pushVal(lookupVarNoException(name) match {
          case -1 =>
            (enumeratorDefs get name) match {
              case Some(e) => e
              case None => throw new TranslationException(
                getLineString(exp) + "Symbol " + name + " is not declared")
            }
          case ind =>
            getValue(ind, false)
        })
      }

      case exp : Econst => evalHelp(exp.constant_)
      case exp : Estring => // todo: implement this properly
        warn("ignoring string argument")
        val srcInfo = Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))
        pushVal(CCTerm(IIntLit(IdealInt(1)), CCInt(), srcInfo))

      case exp : Earray =>
        val srcInfo = Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))
        val arrayTerm : CCExpr = eval(exp.exp_1)
        val index : CCExpr = eval(exp.exp_2)

        import IExpression._
        arrayTerm.typ match {
          case array : CCHeapArrayPointer =>
            pushVal(heapArrayRead(arrayTerm, index, array))
          case array : CCArray => // todo: move to separate method
            val readValue = CCTerm(array.arrayTheory.
              select(arrayTerm.toTerm, index.toTerm), array.elementType, srcInfo)
            array.sizeExpr match {
              case Some(expr) =>
                assertProperty((index.toTerm >= 0) &&&
                  (index.toTerm < expr.toTerm), srcInfo)
              case _ => // no safety assertion needed for mathematical arrays
            }
            pushVal(readValue)
          case _ =>
            throw new TranslationException(getLineString(exp) +
              arrayTerm + " is not an array type!")
        }
      case exp : Ebytesexpr =>
        throw new TranslationException(getLineString(exp) +
          "Ebytesexpr currently not supported by TriCera: " +
          (printer print exp))
      case exp: Ebytestype => // Adding support for sizeof()
        exp.type_name_ match {
          case pt : PlainType =>
            pt.listspec_qual_.getFirst() match {
              case ts : TypeSpec =>
                ts.type_specifier_ match {
                  case _ : Tint => //TODO: check what size should be int, now assumes sizeof(int) is 4
                    pushVal(CCTerm(IExpression.i(IdealInt("4")), CCInt(),
                      Some(SourceInfo(exp.line_num, exp.col_num, exp.offset))))
                  case _ => // Only int supported for now
                    throw new TranslationException(getLineString(exp) +
                      "Only int byteexprs currently supported by TriCera: " +
                      (printer print exp))
                }
              case _  => throw new TranslationException(getLineString(exp) +
                "Qual stuff currently not supported by TriCera: " +
                (printer print exp))
            }

          case _ => throw new TranslationException(getLineString(exp) +
            "Ebytestype currently not supported by TriCera for extended types: " +
            (printer print exp))
        }
            exp: Enondet =>
        throw new TranslationException(getLineString(exp) +
          "Enondet currently not supported by TriCera: " +
          (printer print exp))

      case _ =>
        throw new TranslationException(getLineString(exp) +
          "Expression currently not supported by TriCera: " +
          (printer print exp))
    }

    private def handleFunction(name : String,
                               functionEntry : CCPredicate,
                               argNum : Int) =
      functionContexts get name match {
        case Some(ctx) => {
          // use the contract of the function
//          assert(!(pointerArgs exists (_.isInstanceOf[CCStackPointer])),
//                 "function contracts do not support pointer arguments yet")

          val funDef = functionDefs(name)

          var argTerms : List[ITerm] = List()
          for (_ <- 0 until argNum)
            argTerms = popVal.toTerm :: argTerms

          val postGlobalVars : Seq[ITerm] = // todo : use ctx postglobal?
            for (v <- globalVars.vars)
            yield IExpression.i(v.sort newConstant (v.name + "_post")) // todo: refactor

          val globals : Seq[ITerm] =
            for (n <- 0 until globalVars.size)
            yield getValue(n, false).toTerm

          val prePredArgs : Seq[ITerm] = globals ++ argTerms

          val resVar : Seq[CCVar] = getResVar(getType(funDef))
          val postPredArgs : Seq[ITerm] =
            prePredArgs ++ postGlobalVars ++ resVar.map(c => IConstant(c.term))
            //postGlobalVars ++ argTerms ++ globals ++ resVar.map(c => IConstant(c.term))

          val preAtom  = ctx.prePred(prePredArgs)
          val postAtom = ctx.postPred(postPredArgs)

          assertProperty(preAtom, None) // todo: mark pre atom assertions

          addGuard(postAtom)

          for (((c, t), n) <- (postGlobalVars.iterator zip
                                 globalVars.formalTypes.iterator).zipWithIndex)
            setValue(n, CCTerm(c, t, None), false) // todo: srcInfo?

          resVar match {
            case Seq(v) => pushVal(CCTerm(v.term, v.typ, v.srcInfo))
            case Seq()  => pushVal(CCTerm(0, CCVoid(), None)) // push a dummy result
          }
        }
        case None => {
          uninterpPredDecls get name match {
            case Some(predDecl) =>
              var argTerms : List[ITerm] = List()
              for (_ <- 0 until argNum)
                argTerms = popVal.toTerm :: argTerms
              pushVal(CCFormula(predDecl(argTerms), CCInt(), None)) // todo:srcInfo
            case None =>
              val args =
                (for (_ <- 0 until argNum) yield popVal.typ).toList.reverse
              // get rid of the local variables, which are later
              // replaced with the formal arguments
              // pointer arguments are saved and passed on
              callFunctionInlining(name, functionEntry, args)
          }
        }
      }

    private def callFunctionInlining(name : String,
                                     functionEntry : CCPredicate,
                                     pointerArgs : List[CCType] = Nil) =
      (functionDefs get name) match {
        case Some(fundef) => {
          val typ = getType(fundef)
          val isNoReturn = (typ.isInstanceOf[CCVoid])
          val exitVar =
            if (isNoReturn) Nil
            else List(new CCVar("_" + name + "Ret", None, typ)) // todo: return line no?
          val srcInfo = Some(FuncDef(fundef).sourceInfo)
          val functionExit = newPred(exitVar, srcInfo) // todo: return line no?

          inlineFunction(fundef, functionEntry, functionExit, pointerArgs,
            isNoReturn)

          // reserve an argument for the function result

          if (typ.isInstanceOf[CCVoid])
            pushFormalVal(CCInt())
          else
            pushFormalVal(typ)
          resetFields(functionExit.pred)
        }
        case None => (functionDecls get name) match {
          case Some((fundecl, typ)) => {
            if (!(name contains "__VERIFIER_nondet" ))
              warn("no definition of function \"" + name + "\" available")
            pushFormalVal(typ)
          }
          case None =>
            throw new TranslationException(
              "Function " + name + " is not declared")
        }
      }

    private def checkPointerIntComparison(t1 : CCExpr, t2 : CCExpr) :
      (CCExpr, CCExpr) =
      (t1.typ, t2.typ) match {
        case (_ : CCHeapPointer, _ : CCArithType) =>
          if (t2.toTerm != IIntLit(IdealInt(0)))
            throw new TranslationException("Pointers can only compared with `null` or `0`.")
          else
            (t1, CCTerm(heap.nullAddr(), t1.typ, t1.srcInfo)) // 0 to nullAddr()
        case (_: CCArithType, _: CCHeapPointer) =>
          if (t1.toTerm != IIntLit(IdealInt(0)))
            throw new TranslationException("Pointers can only compared with `null` or `0`.")
          else
            (CCTerm(heap.nullAddr(), t2.typ, t2.srcInfo), t2) // 0 to nullAddr()
        case _ => (t1, t2)
      }

    private def strictBinOp(left : Exp, right : Exp,
                            op : (CCExpr, CCExpr) => CCExpr) : Unit = {
      evalHelp(left)
      maybeOutputClause
      evalHelp(right)
      val rhs = popVal
      val lhs = popVal
      val (actualLhs, actualRhs) = checkPointerIntComparison(lhs, rhs) // todo: not correct for ops except === and =/=, refactor or add check
      pushVal(op(actualLhs, actualRhs))
    }

    ////////////////////////////////////////////////////////////////////////////

    /* lhs must be an address range term, used for pointer arithmetic
    *  operations, e.g. when p += 1 rhs is 1 and op is +
    * */
    private def addToAddressRangeStart (lhs : ITerm, rhs : ITerm): ITerm = {
      heap.addressRangeCtor(heap.nth(lhs, rhs), heap.addrRangeSize(lhs) - rhs)
    }

    private def strictBinFun(left : Exp, right : Exp,
                             op : (ITerm, ITerm) => ITerm,
                             opIsAddition : Boolean = false) : Unit = {
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) => {
                    (lhs.typ, rhs.typ) match {
                      case (arrTyp: CCHeapArrayPointer, _ : CCArithType) =>
                        if(opIsAddition)
                          CCTerm(addToAddressRangeStart(lhs.toTerm, rhs.toTerm),
                                 arrTyp, lhs.srcInfo)
                        else
                          throw new TranslationException("Pointer arithmetic" +
                            "over arrays is only supported with addition.")
                      case _ =>
                        val (promLhs, promRhs) = unifyTypes(lhs, rhs)
                        // TODO: correct type promotion
                        val typ = promLhs.typ
                        CCTerm(typ cast op(promLhs.toTerm, promRhs.toTerm), typ,
                               lhs.srcInfo)
                    }
                   })
    }

    private def strictUnsignedBinFun(left : Exp, right : Exp,
                                     op : (ITerm, ITerm) => ITerm) : Unit = {
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) => {
                     val (promLhs, promRhs) = unifyTypes(lhs, rhs)
                     // TODO: correct type promotion
                     val typ = promLhs.typ
                     CCTerm(typ cast op(typ cast2Unsigned promLhs.toTerm,
                                        typ cast2Unsigned promRhs.toTerm),
                            typ, lhs.srcInfo)
                   })
    }

    private def strictBinPred(left : Exp, right : Exp,
                              op : (ITerm, ITerm) => IFormula) : Unit = {
      import IExpression._
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) => (lhs.typ, rhs.typ) match {
                    case (_ : CCClock, _ : CCArithType) =>
                      CCFormula(op(GT.term - lhs.toTerm,
                                   GTU.term * rhs.toTerm), CCInt(), lhs.srcInfo)
                    case (_ : CCArithType, _ : CCClock) =>
                      CCFormula(op(GTU.term * lhs.toTerm,
                                   GT.term - rhs.toTerm), CCInt(), lhs.srcInfo)
                    case (_ : CCClock, _ : CCClock) =>
                      CCFormula(op(-lhs.toTerm, -rhs.toTerm), CCInt(), lhs.srcInfo)

                    case (_ : CCDuration, _ : CCArithType) =>
                      CCFormula(op(lhs.toTerm, GTU.term * rhs.toTerm), CCInt(), lhs.srcInfo)
                    case (_ : CCArithType, _ : CCDuration) =>
                      CCFormula(op(GTU.term * lhs.toTerm, rhs.toTerm), CCInt(), lhs.srcInfo)
                    case (_ : CCDuration, _ : CCDuration) =>
                      CCFormula(op(lhs.toTerm, rhs.toTerm), CCInt(), lhs.srcInfo)

                    case (_ : CCClock, _ : CCDuration) =>
                      CCFormula(op(GT.term - lhs.toTerm, rhs.toTerm), CCInt(), lhs.srcInfo)
                    case (_ : CCDuration, _ : CCClock) =>
                      CCFormula(op(lhs.toTerm, GT.term - rhs.toTerm), CCInt(), lhs.srcInfo)
                    case _ =>
                      CCFormula(op(lhs.toTerm, rhs.toTerm), CCInt(), lhs.srcInfo)
                  })
    }

    ////////////////////////////////////////////////////////////////////////////

    private def convertType(t : CCExpr, newType : CCType) : CCExpr =
      (t.typ, newType) match {
        case (oldType, newType)
          if (oldType == newType) =>
            t
        case (oldType : CCArithType, newType : CCArithType) =>
          newType cast t
        case (oldType : CCArithType, _ : CCDuration) => {
          if (!useTime)
            throw NeedsTimeException
          import IExpression._
          CCTerm(GTU.term * t.toTerm, CCDuration(), t.srcInfo)
        }
        // newType is actually heap pointer
        //case (oldType : CCHeapPointer, newType : CCStackPointer) =>
        //  newType.typ cast t
        case (_ , _ : CCVoid) =>  t // todo: do not do anything for casts to void?
        case (oldType : CCArithType, newType : CCHeapPointer) =>
          t.toTerm match {
            case lit: IIntLit if lit.value.intValue == 0 =>
              CCTerm(heap.nullAddr(), newType, t.srcInfo) //newType cast t
            case _ => throw new TranslationException(
              "pointer arithmetic is not allowed, cannot convert " + t + " to " +
                newType)
          }
        case (oldType : CCHeapPointer, newType : CCHeapPointer) =>
          newType cast t
        case _ =>
          throw new TranslationException(
            "do not know how to convert " + t.typ + " to " + newType +
              " for term: " + t.toTerm + " (srcInfo: " + t.srcInfo + ")")
      }

    private def unifyTypes(a : CCExpr, b : CCExpr) : (CCExpr, CCExpr) = {
      (a.typ, b.typ) match {
        case (at, bt) if (at == bt) =>
          (a, b)

        case (at: CCArithType, bt: CCArithType) =>
          if ((at.UNSIGNED_RANGE > bt.UNSIGNED_RANGE) ||
            (at.UNSIGNED_RANGE == bt.UNSIGNED_RANGE && at.isUnsigned))
            (a, convertType(b, at))
          else
            (convertType(a, bt), b)

        case (at: CCArithType, _ : CCDuration) =>
          (convertType(a, CCDuration()), b)
        case (_ : CCDuration, bt: CCArithType) =>
          (a, convertType(b, CCDuration()))

        case _ =>
          throw new TranslationException("incompatible types: " +
            a.typ + " vs " + b.typ)
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    private def evalHelp(constant : Constant) : Unit = constant match {
//      case constant : Efloat.        Constant ::= Double;
      case constant : Echar =>
        pushVal(CCTerm(IdealInt(constant.char_.toInt), CCInt(), Some(
          SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Eunsigned =>
        pushVal(CCTerm(IdealInt(
          constant.unsigned_.substring(0,
          constant.unsigned_.size - 1)), CCUInt(), Some(
          SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Elong =>
        pushVal(CCTerm(IdealInt(
          constant.long_.substring(0, constant.long_.size - 1)), CCLong(), Some(
          SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Eunsignlong =>
        pushVal(CCTerm(IdealInt(
          constant.unsignedlong_.substring(0,
          constant.unsignedlong_.size - 2)), CCULong(), Some(
          SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Ehexadec =>
        pushVal(CCTerm(IdealInt(constant.hexadecimal_ substring 2, 16), CCInt(),
          Some(SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Ehexaunsign =>
        pushVal(CCTerm(IdealInt(constant.hexunsigned_.substring(2,
                                constant.hexunsigned_.size - 1), 16), CCUInt(),
          Some(SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Ehexalong =>
        pushVal(CCTerm(IdealInt(constant.hexlong_.substring(2,
                                constant.hexlong_.size - 1), 16), CCLong(),
          Some(SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Ehexaunslong =>
        pushVal(CCTerm(IdealInt(constant.hexunslong_.substring(2,
                                constant.hexunslong_.size - 2), 16), CCULong(),
          Some(SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant : Eoctal =>
        pushVal(CCTerm(IdealInt(constant.octal_, 8), CCInt(),
          Some(SourceInfo(constant.line_num, constant.col_num, constant.offset))))
//      case constant : Eoctalunsign.  Constant ::= OctalUnsigned;
      case constant : Eoctallong =>
        pushVal(CCTerm(IdealInt(constant.octallong_.substring(0,
                                constant.octallong_.size - 1), 8), CCLong(),
          Some(SourceInfo(constant.line_num, constant.col_num, constant.offset))))
//      case constant : Eoctalunslong. Constant ::= OctalUnsLong;
//      case constant : Ecdouble.      Constant ::= CDouble;
//      case constant : Ecfloat.       Constant ::= CFloat;
//      case constant : Eclongdouble.  Constant ::= CLongDouble;
      case constant : Eint =>
        pushVal(CCTerm(IExpression.i(IdealInt(constant.unboundedinteger_)), CCInt(),
          Some(SourceInfo(constant.line_num, constant.col_num, constant.offset))))
      case constant => throw new TranslationException("Unimplemented type: " +
        constant.getClass)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def inlineFunction(functionDef : Function_def,
                             entry : CCPredicate,
                             exit : CCPredicate,
                             args : List[CCType],
                             isNoReturn : Boolean) : Unit = {
    localVars pushFrame
    val stm = pushArguments(functionDef, args)

    assert(entry.arity == allFormalVars.size)

    val translator = FunctionTranslator(exit)
    val finalPred =
      if (isNoReturn) {
        translator.translateNoReturn(stm, entry)
        exit
      } else
        translator.translateWithReturn(stm, entry)
    functionExitPreds += ((FuncDef(functionDef).name, finalPred))
    localVars popFrame
  }

  private def createHeapPointer(decl : BeginPointer, typ : CCType) :
  CCHeapPointer = createHeapPointerHelper(decl.pointer_, typ)

  private def createHeapPointerHelper(decl : Pointer, typ : CCType) :
  CCHeapPointer = decl match {
      case pp : PointPoint =>
        CCHeapPointer(heap, createHeapPointerHelper(pp.pointer_, typ))
      case p : Point =>
        CCHeapPointer(heap, typ)
      case _ => throw new TranslationException("Type qualified pointers are " +
        "currently not supported: " + decl)
    }

  private def pushArguments(functionDef : Function_def,
                            pointerArgs : List[CCType] = Nil) : Compound_stm = {
    val f = FuncDef(functionDef)
    val decl = f.decl match {
      case noPtr : NoPointer => noPtr.direct_declarator_
      case ptr   : BeginPointer => ptr.direct_declarator_
    }
    decl match {
      case dec : NewFuncDec =>
        val decList = dec.parameter_type_.asInstanceOf[AllSpec]
          .listparameter_declaration_
        for (ind <- decList.indices)
          decList(ind) match {
            case _ : OnlyType =>
              // ignore, a void argument implies that there are no arguments
            case argDec : TypeAndParam => {
              val name = getName(argDec.declarator_)
              val typ = getType(argDec.listdeclaration_specifier_)
              val actualType = argDec.declarator_ match {
                case _: BeginPointer if pointerArgs.nonEmpty => pointerArgs(ind)
                case p : BeginPointer =>
                  createHeapPointer(p, typ)
                case np : NoPointer =>
                  np.direct_declarator_ match {
                    case _ : Incomplete if !TriCeraParameters.parameters.value.useArraysForHeap =>
                      CCHeapArrayPointer(heap, typ, HeapArray)
                    case _ : Incomplete if TriCeraParameters.parameters.value.useArraysForHeap =>
                      CCArray(typ, None, None, ExtArray(Seq(CCInt().toSort), typ.toSort), HeapArray)
                    case _ => typ
                  }
                case _ => typ
              }
              val declaredVar = new CCVar(name,
                Some(SourceInfo(argDec.line_num, argDec.col_num, argDec.offset)),
                actualType)
              localVars addVar declaredVar
            }

            case argDec : TypeHintAndParam => {
              val typ = getType(argDec.listdeclaration_specifier_)
              val actualType = argDec.declarator_ match {
                case _: BeginPointer if pointerArgs.nonEmpty => pointerArgs(ind)
                case p : BeginPointer => createHeapPointer(p, typ)
                case _ => typ
              }
              val declaredVar = new CCVar(getName(argDec.declarator_),
                Some(SourceInfo(argDec.line_num, argDec.col_num, argDec.offset)),
                actualType)
              localVars addVar declaredVar
              processHints(argDec.listannotation_)
            }
//            case argDec : Abstract =>
          }
//      case dec : OldFuncDef =>
//        for (ident <- dec.listcident_)
//          localVars += new ConstantTerm(ident)
      case dec : OldFuncDec =>
        // arguments are not specified ...
    }
    f.body
  }

  //////////////////////////////////////////////////////////////////////////////

  private object FunctionTranslator {
    def apply =
      new FunctionTranslator(None)
    def apply(returnPred : CCPredicate) =
      new FunctionTranslator(Some(returnPred))
  }

  private class FunctionTranslator private (returnPred : Option[CCPredicate]) {

    private def symexFor(initPred : CCPredicate,
                         stm : Expression_stm) : (Symex, Option[CCExpr]) = {
      val exprSymex = Symex(initPred)
      val res = stm match {
        case _ : SexprOne => None
        case stm : SexprTwo => Some(exprSymex eval stm.exp_)
      }
      (exprSymex, res)
    }



    def translateNoReturn(compound : Compound_stm) : CCPredicate = {
      val finalPred = newPred(Nil, Some(getLastSourceInfo(compound)))
      translateWithEntryClause(compound, finalPred)
      postProcessClauses
      finalPred
    }

    def translateNoReturn(compound : Compound_stm,
                          entry : CCPredicate) : Unit = {
      val finalPred = newPred(Nil, Some(getLastSourceInfo(compound)))
      translate(compound, entry, finalPred)
      // add a default return edge
      val rp = returnPred.get
      output(Clause(atom(rp, allFormalVarTerms take rp.arity),
                    List(atom(finalPred, allFormalVarTerms)),
                    true))
      postProcessClauses
    }

    def translateWithReturn(compound : Compound_stm) : Unit = {
      val finalPred = newPred(Nil, Some(getLastSourceInfo(compound)))
      translateWithEntryClause(compound, finalPred)
      // add a default return edge
      //val rp = returnPred.get
      //output(Clause(atom(rp, (allFormalVars take (rp.arity - 1)) ++
      //                       List(IConstant(new ConstantTerm("__result")))),
      //              List(atom(finalPred, allFormalVars)),
      //              true))
      postProcessClauses
    }

    def translateWithReturn(compound : Compound_stm,
                            entry : CCPredicate) : CCPredicate = {
      val finalPred = newPred(Nil, Some(getLastSourceInfo(compound)))
      translate(compound, entry, finalPred)
      // add a default return edge
      //val rp = returnPred.get
      //output(Clause(atom(rp, (allFormalVars take (rp.arity - 1)) ++
      //                       List(IConstant(new ConstantTerm("__result")))),
      //              List(atom(finalPred, allFormalVars)),
      //              true))
      postProcessClauses
      finalPred
    }

    ////////////////////////////////////////////////////////////////////////////

    private def postProcessClauses : Unit = {
      connectJumps
      mergeAtomicBlocks
    }

    private def connectJumps : Unit =
      for ((label, jumpPred, jumpVars, position) <- jumpLocs)
        (labelledLocs get label) match {
          case Some((targetPred, targetVars)) => {
            val commonVars =
              (jumpVars zip targetVars).takeWhile({
                case (x, y) => x == y
              }).map(_._1)
            val jumpArgs = commonVars ++ (
              for (i <- 0 until (jumpPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("preArg_" + i)))
            val targetArgs = commonVars ++ (
              for (i <- 0 until (targetPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("postArg_" + i)))
            clauses(position) = (Clause(atom(targetPred, targetArgs),
                                        List(atom(jumpPred, jumpArgs)),
                                        true),
                                 ParametricEncoder.NoSync)
            usedJumpTargets.put(targetPred, label)
          }
          case None =>
            throw new TranslationException("cannot goto label " + label)
        }

    private def mergeAtomicBlocks : Unit = if (!atomicBlocks.isEmpty) {
      val sortedBlocks =
        atomicBlocks sortWith { case ((s1, e1), (s2, e2)) =>
                                  s1 < s2 || (s1 == s2 && e1 > e2) }

      val offset = sortedBlocks.head._1
      var concernedClauses = clauses.slice(offset, clauses.size).toList
      clauses reduceToSize offset

      var curPos = offset
      for ((bstart, bend) <- sortedBlocks)
        if (bstart >= curPos) {
          while (curPos < bend) {
            clauses += concernedClauses.head
            concernedClauses = concernedClauses.tail
            curPos = curPos + 1
          }
          mergeClauses(clauses.size - (bend - bstart))
        }

      clauses ++= concernedClauses

      val bodyPreds =
        (for ((c, _) <- clauses.iterator; p <- c.bodyPredicates.iterator)
         yield p).toSet

      for ((Clause(IAtom(pred, _), _, _), _) <- clauses.iterator)
        if (!(bodyPreds contains pred) && (usedJumpTargets contains pred))
          throw new TranslationException("cannot goto label " +
                                         usedJumpTargets(pred) +
                                         ", which was eliminated due to " +
                                         "atomic blocks")
    }

    private val jumpLocs =
      new ArrayBuffer[(String, Predicate, Seq[ITerm], Int)]
    private val labelledLocs =
      new MHashMap[String, (Predicate, Seq[ITerm])]
    private val usedJumpTargets =
      new MHashMap[Predicate, String]
    private val atomicBlocks =
      new ArrayBuffer[(Int, Int)]

    ////////////////////////////////////////////////////////////////////////////

    private def translate(stm : Stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit =
      stm match {
        case stm: LabelS =>
          translate(stm.labeled_stm_, entry, exit)
        case stm: CompS =>
          translate(stm.compound_stm_, entry, exit)
        case stm: ExprS =>
          val symex = symexFor(entry, stm.expression_stm_)._1
          symex outputClause exit.pred
        case stm: SelS =>
          translate(stm.selection_stm_, entry, exit)
        case stm: IterS =>
          translate(stm.iter_stm_, entry, exit)
        case stm: JumpS =>
          translate(stm.jump_stm_, entry, exit)
        case stm: AtomicS =>
          translate(stm.atomic_stm_, entry, exit)
        case stm: AnnotationS => // todo: mvoe this into a separate translate method
          try{translate(stm.annotation_, entry)}
          catch {
            case e : ExtendedQuantifierException => throw e
            case e if TriCeraParameters.get.onlyExtQuans => throw e
            case e : Exception =>
              warn("Ignoring ACSL annotation (possibly " +
                "an error or an unsupported fragment):\n" + e.getMessage)
          }
      }

    private def translate(stm : Annotation, entry : CCPredicate) : Unit = {
      val annotationInfo = AnnotationParser(annotationStringExtractor(stm))
      annotationInfo match {
        case Seq(MaybeACSLAnnotation(annot, _)) =>
          val stmSymex = Symex(entry)
          class LocalContext extends ACSLTranslator.StatementAnnotationContext {
            /**
             * Returns the term from the init atom - this should work as
             * long as the annotation does not have side effects, because
             * it always returns the original terms from initAtom
             */
            override def getTermInScope(name: String): Option[CCTerm] = {
              entry.argVars.zipWithIndex.find {
                case (v, i) => v.name == name
              } match {
                case Some((v, i)) =>
                  stmSymex.initAtomArgs match {
                    case Some(args) => Some(CCTerm(args(i), v.typ, v.srcInfo))
                    case None => None
                  }
                case None => None
              }
            }

            override def getGlobals: Seq[CCVar] = globalVars.vars
            override def sortWrapper(s: Sort): Option[IFunction] =
              sortWrapperMap get s
            override def sortGetter(s: Sort): Option[IFunction] =
              sortGetterMap get s
            override def getCtor(s: Sort): Int = sortCtorIdMap(s)
            override def getTypOfPointer(t: CCType): CCType =
              t match {
                case p: CCHeapPointer => p.typ
                case t => t
              }
            override implicit val arithMode = arithmeticMode
            override def isHeapEnabled: Boolean = modelHeap
            override def getHeap: HeapObj =
              if (modelHeap) heap else throw NeedsHeapModelException
            override def getHeapTerm: ITerm =
              if (modelHeap) stmSymex.getValues.head.toTerm
              else throw NeedsHeapModelException
            override def getOldHeapTerm: ITerm =
              getHeapTerm // todo: heap term for exit predicate?
          }
          ACSLTranslator.translateACSL(
            "/*@" + annot + "*/", new LocalContext()) match {
            case res: tricera.acsl.StatementAnnotation =>
              import IExpression._
//              println(tryGetQuantifiedFormulaInfo(res.f))
              if (res.isAssert) {
                import lazabs.prover.PrincessWrapper._
                tryGetQuantifiedFormulaInfo(res.f) match {
                  case Some(info) =>
                    val reduceOp: (ITerm, ITerm) => ITerm =
                      (a: ITerm, b: ITerm) => info.quantifier match { // a is the aggregate, b is the currently accessed value
                        case Quantifier.ALL =>
                          expr2Term(expr2Formula(a) &&& expr2Formula(b))
                          //ite(expr2Formula(a), b, a) // if a is true, b must be true too
                        case Quantifier.EX =>
                          expr2Term(expr2Formula(a) ||| expr2Formula(b))
                          //ite(expr2Formula(a), a, b) // if a is true, b is ignored, otherwise take b
                      }
                    val predicate : (ITerm, ITerm) => ITerm = // todo: this does not work for cases where other program variables are referred in the predicate
                      (access : ITerm, index : ITerm) =>
                      {
                        // replace the term a[i] with the value being read/written
                        expr2Term(
                          ExpressionReplacingVisitor( // then replace any references to the bound variable with the index term
                            ExpressionReplacingVisitor( // first replace the array access term
                              info.predicate, info.arrayAccess, access),
                            info.arrayIndex, index))
                      }
                    val extQuan = new ExtendedQuantifier(
                      name = info.quantifier match {
                        case Quantifier.ALL => "\\forall"
                        case Quantifier.EX => "\\exists"
                      },
                      arrayTheory = info.arrayTheory,
                      identity = info.quantifier match {
                        case Quantifier.ALL => expr2Term(IBoolLit(true))
                        case Quantifier.EX => expr2Term(IBoolLit(false))
                      },
                      reduceOp = reduceOp,
                      invReduceOp = None,
                      predicate = Some(predicate),
                      rangeFormulaLo = Some(info.quantifier match {
                        case Quantifier.ALL =>
                          (ghostLo: ITerm, lo: ITerm, p : ITerm) =>
                            ite(expr2Formula(p), ghostLo <= lo, ghostLo >= lo)
                        // true for the larger range
                        case Quantifier.EX =>
                          (ghostLo: ITerm, lo: ITerm, p : ITerm) =>
                            ite(expr2Formula(p), ghostLo >= lo, ghostLo <= lo)
                        // true for the smaller range
                      }),
                      rangeFormulaHi = Some(info.quantifier match {
                        case Quantifier.ALL =>
                          (ghostHi: ITerm, hi: ITerm, p : ITerm) =>
                            ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)
                             // true for the larger range
                        case Quantifier.EX =>
                          (ghostHi: ITerm, hi: ITerm, p : ITerm) =>
                            ite(expr2Formula(p), ghostHi <= hi, ghostHi >= hi)
                            // true for the smaller range
                      }))
                    TheoryRegistry register extQuan
                    stmSymex.assertProperty(
                      expr2Formula(extQuan.fun(info.arrayTerm, info.lo, info.hi)),
                      srcInfo = Some(getSourceInfo(stm))
                    )
                  case None =>
                    stmSymex.assertProperty(res.f, Some(getSourceInfo(stm)))
                }
              } else
                warn("Ignoring annotation: " + annot)
            case _ => warn("Ignoring annotation: " + annot)
          }
        case _ => warn("Ignoring annotation: " + annotationInfo)
      }
    }

    private case class QuantifiedFormulaInfo(quantifier : IExpression.Quantifier,
                                             lo : ITerm, // inclusive
                                             hi : ITerm, // exclusive
                                             arrayTerm : ITerm,
                                             predicate : IFormula,
                                             arrayAccess : IFunApp,
                                             arrayIndex : ITerm,
                                             arrayTheory : ExtArray,
                                             originalF : IFormula)
    /**
     * Given a quantified formula, tries to extract ranges and the predicate.
     * This is very basic and only extracts when the quantified formula is in
     * one of two shapes:
     *  1. ALL i. (! ((i + -1*lo) >= 0 & ((hi + -1*i) + -1) >= 0) | predicate
     *    (or forall int i; lo <= i < hi ==> predicate)
     *  2. EX  i. ...
     *    (or exists int i; lo <= i < hi & predicate)
     */
    private def tryGetQuantifiedFormulaInfo(f : IFormula) :
      Option[QuantifiedFormulaInfo] = {
      import IExpression._

      def extractInfo(flo: IFormula,
                      fhi: IFormula,
                      pred: IFormula,
                      quan: IExpression.Quantifier):
      Option[QuantifiedFormulaInfo] = {
        // try to extract the lo term
        val maybeLo = flo match {
          case GeqZ(IVariable(0)) => // _0 >= 0 // lo is 0
            Some(i(0))
          case GeqZ(IPlus(IVariable(0), IIntLit(IdealInt(loMinus)))) => // _0 >= c // lo is c
            Some(i(-loMinus))
          case GeqZ(IPlus(IVariable(0), ITimes(IdealInt(-1), lo))) => // _0 + -1*lo >= 0 or (_0 >= lo)
            Some(lo)
          case _ => None
        }
        // try to extract the hi term
        val maybeHi = fhi match {
          case GeqZ(IPlus(IPlus(hi, ITimes(IdealInt(-1), IVariable(0))), IIntLit(IdealInt(-1)))) => // hi + -1*_0 + -1 >= 0 or (hi > _0)
            Some(hi)
          case _ => None
        }
        // try to extract the array access from the predicate,
        // current implementation supports only a single array access
        // to the bound variable, i.e., a[j]. predicates with
        // more accesses, e.g., a[i] < a[i + 1], are currently
        // unsupported.
        object ArraySelectExtractor extends TheoryExtractor {
          override def unapply(f: IFunction): Option[Theory] =
            ExtArray.Select.unapply(f)
        }
        val selectCollector =
          new FunAppsFromExtractorCollector(ArraySelectExtractor)
        val (selects, theories) =
          selectCollector.visit(pred, 0).unzip
        // ensure that all selects are to the same array variable,
        // to the same index term and to the same theory

        val maybeArrayAccess: Option[(IFunApp, ExtArray)] =
          if (theories.nonEmpty &&
            theories.forall(theory => theory == theories.head)) {
            // a select is found and all theories are the same
            if (selects.forall { select =>
              select.args == selects.head.args
            }) {
              // all selects access the same array and index -> todo: support accesses like a[i] ... a[i + 1]
              Some((selects.head, theories.head.asInstanceOf[ExtArray]))
            } else None
          } else None

        if (maybeLo.nonEmpty && maybeHi.nonEmpty &&
          maybeArrayAccess.nonEmpty) {
          val (select, theory) = maybeArrayAccess.get
          Some(QuantifiedFormulaInfo(
            quantifier = quan,
            arrayTerm = select.args.head,
            lo = maybeLo.get,
            hi = maybeHi.get,
            predicate = pred,
            arrayAccess = select,
            arrayIndex = select.args.last,
            arrayTheory = theory,
            originalF = f))
        } else if (TriCeraParameters.get.onlyExtQuans) {
          throw new ExtendedQuantifierException("Could not encode general quantifier as an " +
            "extended quantifier: " + f)
        }
          else None
      }

      f match {
        case IQuantified(quan, subf) =>
          quan match {
            case Quantifier.ALL =>
              subf match {
                case Disj(fRange, pred) =>
                  fRange match {
                    case INot(Conj(flo, fhi)) => extractInfo(flo, fhi, pred, quan)
                    case _ => throw new ExtendedQuantifierException("Could not encode general quantifier as an " +
                      "extended quantifier: " + f)
                  }
                case _ => None
              }
            case Quantifier.EX =>
              subf match {
                case Conj(fRange, pred) =>
                  fRange match {
                    case Conj(flo, fhi) => extractInfo(flo, fhi, pred, quan)
                    case _ => throw new ExtendedQuantifierException("Could not encode general quantifier as an " +
                      "extended quantifier: " + f)
                  }
                case _ => None
              }
            // todo: support for extracting existential quantifiers to be
            //  used for instrumentation
          }
        case _ => None
      }
    }

    private def translate(dec : Dec, entry : CCPredicate) : CCPredicate = {
      val decSymex = Symex(entry)
      collectVarDecls(dec, false, decSymex)
      val exit = newPred(Nil, Some(getSourceInfo(dec)))
      decSymex outputClause exit.pred
      exit
    }

    private def translate(stm : Labeled_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = stm match {
      case stm : SlabelOne => { // Labeled_stm ::= CIdent ":" Stm ;
        if (labelledLocs contains stm.cident_)
          throw new TranslationException("multiple labels " + stm.cident_)
        labelledLocs.put(stm.cident_, (entry.pred, allFormalVarTerms))
        translate(stm.stm_, entry, exit)
      }
      case stm : SlabelTwo => { // Labeled_stm ::= "case" Constant_expression ":" Stm ;
        val caseVal = translateConstantExpr(stm.constant_expression_)
        innermostSwitchCaseCollector += ((caseVal, entry))
        translate(stm.stm_, entry, exit)
      }
      case stm : SlabelThree => { // . Labeled_stm ::= "default" ":" Stm;
        innermostSwitchCaseCollector += ((null, entry))
        translate(stm.stm_, entry, exit)
      }
    }

    private def translateWithEntryClause(
                          compound : Compound_stm,
                          exit : CCPredicate) : Unit = compound match {
      case compound : ScompOne =>
        output(Clause(atom(exit, allVarInits), List(), globalPreconditions))
      case compound : ScompTwo => {
        localVars pushFrame

        val stmsIt = ap.util.PeekIterator(compound.liststm_.iterator)

        // merge simple side-effect-free declarations with
        // the entry clause
        var entryPred = newPred(Nil,
          if(stmsIt.hasNext) Some(getSourceInfo(stmsIt.peekNext)) else None)
        var entryClause =
          Clause(atom(entryPred, allVarInits), List(), globalPreconditions)

        while (stmsIt.hasNext && isSEFDeclaration(stmsIt.peekNext)) {
          val decSymex = Symex(entryPred)
          collectVarDecls(stmsIt.next.asInstanceOf[DecS].dec_,
                          false, decSymex)
          entryPred = newPred(Nil,
            if(stmsIt.hasNext) Some(getSourceInfo(stmsIt.peekNext)) else None)
          entryClause = merge(decSymex genClause entryPred.pred, entryClause)
        }
        output(entryClause)

        translateStmSeq(stmsIt, entryPred, exit,
                        freeArraysOnStack = trackMemorySafety && modelHeap)
        localVars popFrame
      }
    }

    private def isSEFDeclaration(stm : Stm) : Boolean = stm match {
      case stm: DecS => {
        stm.dec_ match {
          case _ : NoDeclarator => true
          case dec : Declarators =>
            dec.listinit_declarator_ forall {
              case _ : OnlyDecl => true
              case _ : HintDecl => true
              case decl : InitDecl => isSEFInitializer(decl.initializer_)
              case decl : HintInitDecl =>
                decl.initializer_.asInstanceOf[InitExpr].exp_ match {
                  case _ : Econst => true
                  case _ => false
                }
            }
        }
      }
      case _ => false
    }

    private def isSEFInitializer(inits: Initializers) : Boolean =
      inits match {
        case init : AnInit => isSEFInitializer(init.initializer_)
        case init : MoreInit => isSEFInitializer(init.initializer_) &&
                                isSEFInitializer(init.initializers_)
      }
    private def isSEFInitializer(init: Initializer) : Boolean =
      init match {
        case decl: InitExpr => decl.exp_ match {
          case _ : Econst => true
          case _ => false
        }
        case _ : InitListOne | _ : InitListTwo =>
          val inits = init match {
            case decl : InitListOne => decl.initializers_
            case decl : InitListTwo => decl.initializers_
          }
          isSEFInitializer(inits)
      }

    private def translate(compound : Compound_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = compound match {
      case compound : ScompOne => {
        val vars = allFormalVarTerms
        output(Clause(atom(exit, vars), List(atom(entry, vars)), true))
      }
      case compound : ScompTwo => {
        localVars pushFrame

        val stmsIt = compound.liststm_.iterator
        translateStmSeq(stmsIt, entry, exit,
                        freeArraysOnStack = trackMemorySafety && modelHeap)
        localVars popFrame
      }
    }

    private def translateStmSeq(stmsIt : Iterator[Stm],
                                entry : CCPredicate,
                                exit : CCPredicate,
                                freeArraysOnStack : Boolean = false) : Unit = {
      var prevPred = entry
      while (stmsIt.hasNext)
        stmsIt.next match {
          case stm : DecS => {
            prevPred = translate(stm.dec_, prevPred)
            if (!stmsIt.hasNext) {
              if (freeArraysOnStack) {
                // free stack allocated arrays that use the theory of heap
                val freeSymex = Symex(prevPred)
                for (v <- localVars.getVarsInTopFrame) v.typ match {
                  case a : CCHeapArrayPointer if a.arrayLocation == StackArray =>
                    freeSymex.heapFree(CCTerm(v.term, v.typ, v.srcInfo))
                    prevPred = newPred(Nil, None) // todo: line no?
                    freeSymex.outputClause(prevPred.pred)
                  case _ => // nothing
                }
                freeSymex.outputClause(exit.pred)
              } else {
                output(Clause(atom(exit, allFormalVarTerms),
                  List(atom(prevPred, allFormalVarTerms)),
                  true))
              }
            }
          }
          case stm => {
            var nextPred = if (stmsIt.hasNext || freeArraysOnStack) newPred(Nil, None) // todo: line no?
                           else exit
            translate(stm, prevPred, nextPred)
            if (freeArraysOnStack && !stmsIt.hasNext) {
              // free stack allocated arrays that use the theory of heap
              val freeSymex = Symex(nextPred)
              for (v <- localVars.getVarsInTopFrame) v.typ match {
                case a : CCHeapArrayPointer if a.arrayLocation == StackArray =>
                  freeSymex.heapFree(CCTerm(v.term, v.typ, v.srcInfo)) // todo: line no probably incorrect
                  nextPred = newPred(Nil, v.srcInfo)  // todo: line no probably incorrect
                  freeSymex.outputClause(nextPred.pred)
                case _ => // nothing
              }
              freeSymex.outputClause(exit.pred)
            }
            prevPred = nextPred
          }
        }
    }

    type SwitchCaseCollector = ArrayBuffer[(CCExpr, CCPredicate)]

    var innermostLoopCont : CCPredicate = null
    var innermostLoopExit : CCPredicate = null
    var innermostSwitchCaseCollector : SwitchCaseCollector = null

    private def withinLoop[A](
                     loopCont : CCPredicate, loopExit : CCPredicate)
                     (comp : => A) : A = {
      val oldCont = innermostLoopCont
      val oldExit = innermostLoopExit
      innermostLoopCont = loopCont
      innermostLoopExit = loopExit
      try {
        comp
      } finally {
        innermostLoopCont = oldCont
        innermostLoopExit = oldExit
      }
    }

    private def withinSwitch[A](
                     switchExit : CCPredicate,
                     caseCollector : SwitchCaseCollector)
                     (comp : => A) : A = {
      val oldExit = innermostLoopExit
      val oldCollector = innermostSwitchCaseCollector
      innermostLoopExit = switchExit
      innermostSwitchCaseCollector = caseCollector
      try {
        comp
      } finally {
        innermostLoopExit = oldExit
        innermostSwitchCaseCollector = oldCollector
      }
    }

    private def translate(stm : Iter_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = stm match {
      case stm : SiterOne => {
        // while loop

        val first = newPred(Nil, entry.srcInfo)

        if (TriCeraParameters.get.inferLoopInvariants)
          addLoopInvariant(entry,
            SourceInfo(stm.line_num, stm.col_num, stm.offset)) // todo: expand util for extracting srcInfo from stmt

        val condSymex = Symex(entry)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, first.pred, exit.pred)
        withinLoop(entry, exit) {
          translate(stm.stm_, first, entry)
        }
      }

      case stm : SiterTwo => {
        // do ... while loop

        val srcInfo = getSourceInfo(stm)
        val first = newPred(Nil, Some(srcInfo))

        if (TriCeraParameters.get.inferLoopInvariants)
          addLoopInvariant(first, srcInfo) // todo: expand util for extracting srcInfo from stmt

        withinLoop(first, exit) {
          translate(stm.stm_, entry, first)
        }

        val condSymex = Symex(first)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, entry.pred, exit.pred)
      }

      case _ : SiterThree | _ : SiterFour => {
        // for loop

        val srcInfo = getSourceInfo(stm)
        val first, second, third = newPred(Nil, Some(srcInfo)) // todo: line no might not be correct

        val (initStm, condStm, body) = stm match {
          case stm : SiterThree =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
          case stm : SiterFour  =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
        }

        if (TriCeraParameters.get.inferLoopInvariants)
          addLoopInvariant(first, srcInfo) // todo: expand util for extracting srcInfo from stmt

        symexFor(entry, initStm)._1 outputClause first.pred

        val (condSymex, condExpr) = symexFor(first, condStm)
        val cond : IFormula = condExpr match {
          case Some(expr) => expr.toFormula
          case None       => true
        }

        condSymex.outputITEClauses(cond, second.pred, exit.pred)

        import HornClauses._
        withinLoop(third, exit) {
          translate(body, second, third)
        }

        stm match {
          case stm : SiterThree =>
            output(first(allFormalVars) :- third(allFormalVarTerms))
          case stm : SiterFour  => {
            val incSymex = Symex(third)
            incSymex eval stm.exp_
            incSymex outputClause first.pred
          }
        }
      }
    }

    private def translate(stm : Selection_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = stm match {
      case _ : SselOne | _ : SselTwo => { // if
        val condSymex = Symex(entry)
        val (cond, srcInfo1, srcInfo2) = stm match {
          case stm : SselOne =>
            ((condSymex eval stm.exp_).toFormula,
              getSourceInfo(stm), getSourceInfo(stm))
          case stm : SselTwo =>
            ((condSymex eval stm.exp_).toFormula,
              getSourceInfo(stm.stm_1), getSourceInfo(stm.stm_2))
        }
        val first = newPred(Nil, Some(srcInfo1))
        val second = newPred(Nil, Some(srcInfo2))
        val vars = allFormalVarTerms

        condSymex.outputITEClauses(cond, first.pred, second.pred)
        stm match {
          case stm : SselOne => {
            translate(stm.stm_, first, exit)
            output(Clause(atom(exit, vars), List(atom(second, vars)), true))
          }
          case stm : SselTwo => {
            translate(stm.stm_1, first, exit)
            translate(stm.stm_2, second, exit)
          }
        }
      }

      case stm : SselThree => {  // switch
        import IExpression._
        val selectorSymex = Symex(entry)
        val selector = (selectorSymex eval stm.exp_).toTerm

        val newEntry = newPred(Nil, Some(getSourceInfo(stm)))
        val collector = new SwitchCaseCollector

        withinSwitch(exit, collector) {
          translate(stm.stm_, newEntry, exit)
        }

        // add clauses for the various cases of the switch
        val (defaults, cases) = collector partition (_._1 == null)
        val guards = for ((value, _) <- cases) yield (selector === value.toTerm)

        for (((_, target), guard) <- cases.iterator zip guards.iterator) {
          selectorSymex.saveState
          selectorSymex addGuard guard
          selectorSymex outputClause target.pred
          selectorSymex.restoreState
        }

        defaults match {
          case Seq() =>
            // add an assertion that we never try to jump to a case that
            // does not exist. TODO: add a parameter for this?
            selectorSymex assertProperty(or(guards),
              Some(SourceInfo(stm.line_num, stm.col_num, stm.offset)))
          case Seq((_, target)) => {
            selectorSymex.saveState
            selectorSymex addGuard ~or(guards)
            selectorSymex outputClause target.pred
            selectorSymex.restoreState
          }
          case _ =>
            throw new TranslationException("multiple default cases in switch")
        }
      }
    }

    private def translate(jump : Jump_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = jump match {
      case jump : SjumpOne => { // goto
        jumpLocs += ((jump.cident_, entry.pred, allFormalVarTerms, clauses.size))
        // reserve space for the later jump clause
        output(null)
      }
      case jump : SjumpTwo => { // continue
        if (innermostLoopCont == null)
          throw new TranslationException(
            "\"continue\" can only be used within loops")
        Symex(entry) outputClause innermostLoopCont.pred
      }
      case jump : SjumpThree => { // break
        if (innermostLoopExit == null)
          throw new TranslationException(
            "\"break\" can only be used within loops")
        Symex(entry) outputClause innermostLoopExit.pred
      }
      case jump : SjumpFour => // return
        returnPred match {
          case Some(rp) => {
            var nextPred = entry
            if (modelHeap && trackMemorySafety) {
              // free stack allocated arrays that use the theory of heap
              val freeSymex = Symex(entry)
              for (v <- localVars.getVarsInTopFrame) v.typ match {
                case a : CCHeapArrayPointer if a.arrayLocation == StackArray =>
                  freeSymex.heapFree(CCTerm(v.term, v.typ, v.srcInfo)) // line no probably incorrect
                  nextPred = newPred(Nil, Some(getSourceInfo(jump)))
                  freeSymex.outputClause(nextPred.pred)
                case _ => // nothing
              }
            }
            val args = allFormalVarTerms take (rp.arity)
            output(Clause(atom(rp, args),
                          List(atom(nextPred, allFormalVarTerms)),
                          true))
          }
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      case jump : SjumpFive => { // return exp
        val symex = Symex(entry)
        val retValue = symex eval jump.exp_
        returnPred match {
          case Some(rp) => {
            if (modelHeap && trackMemorySafety) {
              localVars.pushFrame
              localVars.addVar(rp.argVars.last)
              val srcInfo = getSourceInfo(jump) // todo: correct line no?
              var nextPred = newPred(Nil, Some(srcInfo))
              val args = symex.getValuesAsTerms ++ List(retValue.toTerm)
              symex outputClause atom(nextPred, args) //output one clause in case return expr modifies heap
              val freeSymex = Symex(nextPred) // reinitialise init atom
              // free stack allocated arrays that use the theory of heap
              for (v <- localVars.getVarsInTopFrame) v.typ match {
                case a : CCHeapArrayPointer if a.arrayLocation == StackArray =>
                  freeSymex.heapFree(CCTerm(v.term, v.typ, v.srcInfo)) // todo: line no probably incorrect
                  nextPred = newPred(Nil, Some(srcInfo))
                  freeSymex.outputClause(nextPred.pred)
                case _ => // nothing
              }
              val retArgs = (freeSymex.getValuesAsTerms take (rp.arity - 1)) ++
                Seq(freeSymex.getValuesAsTerms.last)
              freeSymex outputClause atom(rp.pred, retArgs)
              localVars.popFrame
            } else {
              val args = (symex.getValuesAsTerms take (rp.arity - 1)) ++
                List(retValue.toTerm)
              symex outputClause atom(rp, args)
            }
          }
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      }
      case _ : SjumpAbort | _ : SjumpExit => { // abort() or exit(int status)
        output(Clause(atom(globalExitPred, Nil),
                      List(atom(entry, allFormalVarTerms)),
                      true))
      }
    }

    private def translate(aStm : Atomic_stm,
                          entry : CCPredicate,
                          exit : CCPredicate) : Unit = aStm match {
      case stm : SatomicOne => {
        val currentClauseNum = clauses.size
        inAtomicMode {
          // add a further state inside the block, to correctly
          // distinguish between loops within the block, and a loop
          // around the block
          val first = newPred(Nil, Some(getSourceInfo(stm)))
          val entrySymex = Symex(entry)
          entrySymex outputClause first.pred
          translate(stm.stm_, first, exit)
        }
        atomicBlocks += ((currentClauseNum, clauses.size))
      }
      case stm : SatomicTwo => {
        val currentClauseNum = clauses.size
        inAtomicMode {
          val first = newPred(Nil, Some(getSourceInfo(stm)))
          val condSymex = Symex(entry)
          condSymex.saveState
          val cond = (condSymex eval stm.exp_).toFormula
          if (!condSymex.atomValuesUnchanged)
            throw new TranslationException(
              "expressions with side-effects are not supported in \"within\"")
          import HornClauses._
          timeInvariants += (cond :- atom(entry, allFormalVarTerms))
          condSymex outputClause first.pred
          translate(stm.stm_, first, exit)
        }
        atomicBlocks += ((currentClauseNum, clauses.size))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val system : ParametricEncoder.System = {
    translateProgram

    val singleThreaded =
      processes.size == 1 &&
      processes.head._2 == ParametricEncoder.Singleton

    val predHints =
      (for (p <- ParametricEncoder.allPredicates(processes).iterator;
            maybePreds = predicateHints get p;
            if maybePreds.isDefined;
            if (!maybePreds.get.isEmpty))
       yield (p -> maybePreds.get.toList)).toMap

    val backgroundClauses =
      (for ((_, clauses) <- functionClauses.toSeq.sortBy(_._1);
            c <- clauses) yield c._1) ++
      (for ((_, clauses) <- functionAssertionClauses.toSeq.sortBy(_._1);
            c <- clauses) yield c.clause)
    val backgroundPreds =
      (for (c <- backgroundClauses;
           p <- c.predicates.toSeq.sortBy(_.name);
           if p != HornClauses.FALSE)
      yield p) ++ uninterpPredDecls.values.map(_.pred)

    val backgroundAxioms =
      if (backgroundPreds.isEmpty && backgroundClauses.isEmpty)
        ParametricEncoder.NoBackgroundAxioms
      else
        ParametricEncoder.SomeBackgroundAxioms(backgroundPreds,
                                               backgroundClauses)

    ParametricEncoder.System(processes.toList,
                             if (singleThreaded) {
                               if (useTime) 2 else 0 // todo : anything for heap here? why only 2 if useTime?
                             } else {
                               globalVars.size
                             },
                             None,
                             if (useTime)
                               ParametricEncoder.ContinuousTime(0, 1)
                             else
                               ParametricEncoder.NoTime,
                             timeInvariants,
                             (assertionClauses).map(_.clause).toList,
                             VerificationHints(predHints),
                             backgroundAxioms,
                             otherPredsToKeep =
                               loopInvariants.map(_._2._1.pred).toList)
  }

  // todo: return fun name if inside function assertions?
  def getRelatedAssertions(pred : Predicate) : Seq[CCClause] = {
    (assertionClauses ++ functionAssertionClauses.flatMap(_._2)).filter(
      _.clause.body.exists(_.pred == pred))
  }

  object PredPrintContext extends ReaderMain.PredPrintContext {
    private def getPred (pred : Predicate) : CCPredicate = {
      predCCPredMap get pred match {
        case Some(ccPred) => ccPred
        case None => predCCPredMap find
          (p => "inv_" + p._1.name == pred.name) match {
          case Some(v) => v._2
          case None => throw new TranslationException("Could not find pred: " +
            pred)
        }
      }
    }
    def predWithArgNames (pred : Predicate) : String =
      getPred(pred).toString
    def predWithArgNamesAndLineNumbers (pred : Predicate) : String =
      getPred(pred).toStringWithLineNumbers
    def predArgNames (pred : Predicate) : Seq[String] =
      getPred(pred).argVars.map(_.toString)
    def predSrcInfo (pred : Predicate) : Option[SourceInfo] =
      getPred(pred).srcInfo
    def getFunctionExitPred (funName : String) : Option[CCPredicate] =
      functionExitPreds get funName
  }
}
