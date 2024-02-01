/**
 * Copyright (c) 2024 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package tricera.concurrency.ccreader

import ap.basetypes.IdealInt
import ap.parser.{IFormula, IFunction, IIntLit, ITerm}
import ap.theories.Heap
import tricera.concurrency.CCReader._
import ap.parser.IExpression.{Sort, _}
import ap.theories.bitvectors.ModuloArithmetic._
import ap.types.{MonoSortedIFunction, SortedConstantTerm}
import CCExceptions._
import tricera.Util.{SourceInfo, getLineString, getLineStringShort}

import scala.collection.mutable.{Stack, HashMap => MHashMap}

abstract sealed class CCType {
  def shortName : String

  // todo: make this abstract. nice to have them all in the same place but
  //  would lead to runtime errors if there are missing cases.
  def toSort : Sort = tricera.params.TriCeraParameters.get.arithMode match {
    case ArithmeticMode.Mathematical =>
      this match {
        case CCBool                         => Sort.Bool
        case CCMathInt                      => Sort.Integer
        case typ: CCArithType if typ.isUnsigned => Sort.Nat
        case CCDuration                     => Sort.Nat
        case CCHeap(heap)                   => heap.HeapSort
        case CCStackPointer(_, _, _)        => Sort.Integer
        case CCHeapPointer(heap, _)         => heap.AddressSort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCArray(_, _, _, s, _)         => s.sort
        case CCStruct(ctor, _)              => ctor.resSort
        case CCStructField(n, s)            => s(n).ctor.resSort
        case CCIntEnum(_, _)                => Sort.Integer
        case _                              => Sort.Integer
      }
    case ArithmeticMode.ILP32 =>
      this match {
        case CCBool                         => Sort.Bool
        case CCInt                          => SignedBVSort(32)
        case CCMathInt                      => Sort.Integer
        case CCUInt                         => UnsignedBVSort(32)
        case CCLong                         => SignedBVSort(32)
        case CCULong                        => UnsignedBVSort(32)
        case CCLongLong                     => SignedBVSort(64)
        case CCULongLong                    => UnsignedBVSort(64)
        case CCDuration                     => Sort.Nat
        case CCHeap(heap)                   => heap.HeapSort
        case CCStackPointer(_, _, _)        => Sort.Integer
        case CCHeapPointer(heap, _)         => heap.AddressSort
        case CCArray(_, _, _, s, _)         => s.sort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCStruct(ctor, _)              => ctor.resSort
        case CCStructField(n, s)            => s(n).ctor.resSort
        case CCIntEnum(_, _)                => Sort.Integer
        case _                              => Sort.Integer
      }
    case ArithmeticMode.LP64 =>
      this match {
        case CCBool                         => Sort.Bool
        case CCInt                          => SignedBVSort(32)
        case CCMathInt                      => Sort.Integer
        case CCUInt                         => UnsignedBVSort(32)
        case CCLong                         => SignedBVSort(64)
        case CCULong                        => UnsignedBVSort(64)
        case CCLongLong                     => SignedBVSort(64)
        case CCULongLong                    => UnsignedBVSort(64)
        case CCDuration                     => Sort.Nat
        case CCHeap(heap)                   => heap.HeapSort
        case CCStackPointer(_, _, _)        => Sort.Integer
        case CCHeapPointer(heap, _)         => heap.AddressSort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCArray(_, _, _, s, _)         => s.sort
        case CCStruct(ctor, _)              => ctor.resSort
        case CCStructField(n, s)            => s(n).ctor.resSort
        case CCIntEnum(_, _)                => Sort.Integer
        case _                              => Sort.Integer
      }
    case ArithmeticMode.LLP64 =>
      this match {
        case CCBool                         => Sort.Bool
        case CCInt                          => SignedBVSort(32)
        case CCMathInt                      => Sort.Integer
        case CCUInt                         => UnsignedBVSort(32)
        case CCLong                         => SignedBVSort(32)
        case CCULong                        => UnsignedBVSort(32)
        case CCLongLong                     => SignedBVSort(64)
        case CCULongLong                    => UnsignedBVSort(64)
        case CCDuration                     => Sort.Nat
        case CCHeap(heap)                   => heap.HeapSort
        case CCStackPointer(_, _, _)        => Sort.Integer
        case CCHeapPointer(heap, _)         => heap.AddressSort
        case CCHeapArrayPointer(heap, _, _) => heap.addressRangeSort
        case CCArray(_, _, _, s, _)         => s.sort
        case CCStruct(ctor, _)              => ctor.resSort
        case CCStructField(n, s)            => s(n).ctor.resSort
        case CCIntEnum(_, _)                => Sort.Integer
        case _                              => Sort.Integer
      }
  }

  def rangePred(t : ITerm) : IFormula =
    toSort match {
      case Sort.Nat =>
        t >= 0
      case ModSort(lower, upper) =>
        t >= lower & t <= upper
      case _ => true // includes Integer, HeapAddress,
      // ADTs
    }

  def range : (Option[IdealInt], Option[IdealInt]) = {
    toSort match {
      case Sort.Nat     => (Some(IdealInt(0)), None)
      case Sort.Integer => (None, None)
      case ModSort(lower, upper) =>
        (Some(lower), Some(upper))
      case otherSort =>
        throw new TranslationException(
          "Do not know how to get range for " +
            " sort " + otherSort)
    }
  }

  def newConstant(name : String) : ConstantTerm = toSort newConstant name

  def isPointerType : Boolean =
    this.isInstanceOf[CCHeapPointer] || this.isInstanceOf[CCHeapArrayPointer]
  def isArithType : Boolean = this.isInstanceOf[CCArithType]

  /**
   * @note [[CCExpr.convertToType]] also has some checks regarding conversions,
   *       which does not use this class for casting.
   *       In fact this check would be too strong in some cases (e.g., *p = 0),
   *       checking the values is needed to relax this check, which is not
   *       possible to do in this class.
   */
  private def castIsAllowed(newType : CCType) : Boolean = {
    this match {
      case typ if typ.isArithType   && newType.isPointerType
               || typ.isPointerType && newType.isArithType => false
      case _ => true
    }
  }

  def cast(t: ITerm) : ITerm = toSort match {
    case s : ModSort => cast2Sort(s, t)
    case _ => t
  }

  def cast2Unsigned(t : ITerm) : ITerm = toSort match {
    case SignedBVSort(n) => cast2UnsignedBV(n, t)
    case _               => t
  }

  def cast(e : CCExpr) : CCExpr = {
    if (!castIsAllowed(e.typ)) {
      throw new UnsupportedCastException(
        getLineStringShort(e.srcInfo) +
        " Casts between pointer and arithmetic types are not supported.")
    }
    e match {
      case CCTerm(t, _, srcInfo)    => CCTerm(cast(t), this, srcInfo)
      case CCFormula(f, _, srcInfo) => CCFormula(f, this, srcInfo)
    }
  }

  def getNonDet : ITerm =
    new SortedConstantTerm("_", toSort)

  // todo: make this abstract
  def getZeroInit : ITerm = this match {
    case structType: CCStruct =>
      val const: IndexedSeq[ITerm] =
        for ((_, fieldType) <- structType.sels)
          yield
            fieldType match {
              case CCStructField(name, structs) => structs(name).getZeroInit
              case _                            => fieldType.getZeroInit
            }
      structType.ctor(const: _*)
    case CCHeapPointer(heap, _)         => heap.nullAddr()
    case CCHeapArrayPointer(heap, _, _) => // todo: start = null, but
      // size 0 or 1?
      heap.addressRangeCtor(heap.nullAddr(), IIntLit(1))
    case CCArray(_, _, _, arrayTheory, _) => arrayTheory.const(0)
    case _                                => IIntLit(0)
  }
}

abstract class CCArithType extends CCType {
  val UNSIGNED_RANGE : IdealInt
  val isUnsigned     : Boolean
}

case object CCVoid extends CCType {
  override def toString : String = "void"
  def shortName = "void"
}

// Logical type - only to be used in ghost code & annotations
case object CCBool extends CCType {
  override def toString : String = "boolean"
  def shortName = "boolean"
}

case object CCInt extends CCArithType {
  override def toString : String = "int"
  def shortName = "int"
  val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFF", 16) // 32bit
  val isUnsigned     : Boolean  = false
}

// Logical type - only to be used in ghost code & annotations
case object CCMathInt extends CCType {
  override def toString : String = "integer"
  def shortName = "integer"
}

case object CCUInt extends CCArithType {
  override def toString: String = "unsigned int"
  def shortName = "uint"
  val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFF", 16) // 32bit
  val isUnsigned     : Boolean  = true
}

case object CCLong extends CCArithType {
  override def toString: String = "long"
  def shortName = "long"
  val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
  val isUnsigned     : Boolean  = false
}

case object CCULong extends CCArithType {
  override def toString: String = "unsigned long"
  def shortName = "ulong"
  val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
  val isUnsigned     : Boolean  = true
}

case object CCLongLong extends CCArithType {
  override def toString: String = "long long"
  def shortName = "llong"
  val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
  val isUnsigned     : Boolean  = false
}

case object CCULongLong extends CCArithType {
  override def toString : String = "unsigned long long"
  def shortName = "ullong"
  val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
  val isUnsigned     : Boolean  = true
}

case object CCFloat extends CCType {
  override def toString : String = "float"
  def shortName = "float"
}

case class CCHeap(heap : Heap) extends CCType {
  override def toString : String = heap.toString
  def shortName = "heap"
}

/**
 * typ is either an index into structInfos (if ADT type), or a CCType
 * ptrDepth 0 => not a pointer, 1 => *, 2 => **, ... */
case class FieldInfo(name       : String,
                     typ        : Either[Integer, CCType],
                     ptrDepth   : Integer)

case class StructInfo(name : String, fieldInfos : Seq[FieldInfo])

/**
 * A struct field with a struct type
 */
case class CCStructField(structName : String,
                         structs    : MHashMap[String, CCStruct])
  extends CCType {
  override def toString: String = "field with type: " + structName
  def shortName = "field:" + structName
}

object CCStruct{
  def rawToFullFieldName(structName : String, fieldName : String) =
    s"$structName::$fieldName"
}
case class CCStruct(ctor : MonoSortedIFunction,
                    sels : IndexedSeq[(MonoSortedIFunction, CCType)])
  extends CCType {
  import CCStruct._
  override def toString: String =
    "struct " + ctor.name + ": (" + sels.mkString + ")"
  def shortName = ctor.name
  def getFieldIndex(rawFieldName : String) = sels.indexWhere(
    _._1.name == rawToFullFieldName(shortName, rawFieldName))
  def getFieldIndex(fieldSelector : IFunction) =
    sels.indexWhere(_._1 == fieldSelector)
  def getFieldAddress(nestedSelectors : List[IFunction]) : List[Int] =
    nestedSelectors match {
      case hd :: Nil => getFieldIndex(hd) :: Nil
      case hd :: tl => {
        val ind = getFieldIndex(hd)
        val typ = getFieldType(ind).asInstanceOf[CCStruct]
        ind :: typ.getFieldAddress(tl)
      }
      case Nil => Nil // not possible to reach
    }
  def getFieldType(ind : Int) : CCType = sels(ind)._2 match {
    case CCStructField(name, structs) => structs(name)
    case typ                          => typ
  }
  def getFieldType(fieldAddress : List[Int]) : CCType =
    fieldAddress match {
      case hd :: Nil => getFieldType(hd)
      case hd :: tl =>
        getFieldType(hd)
          .asInstanceOf[CCStruct]
          .getFieldType(tl)
      case Nil =>
        throw new TranslationException(
          "Field type " +
            "requested with" +
            "empty field index!")
    }

  def contains(rawFieldName : String) = getFieldIndex(rawFieldName) != -1
  def getFieldTerm(t : ITerm, fieldAddress: List[Int]): ITerm = {
    val hd :: tl = fieldAddress
    val sel      = getADTSelector(hd)
    getFieldType(hd) match {
      case nested: CCStructField =>
        tl match {
          case Nil => sel(t)
          case _   => nested.structs(nested.structName).getFieldTerm(sel(t), tl)
        }
      case nested: CCStruct => // todo: simplify
        tl match {
          case Nil => sel(t)
          case _   => nested.getFieldTerm(sel(t), tl)
        }
      case _ => sel(t)
    }
  }
  def setFieldTerm(rootTerm:     ITerm,
                   setVal:       ITerm,
                   fieldAddress: List[Int]): ITerm = {
    fieldAddress match {
      case hd :: tl => {
        val childTerm = getFieldType(hd) match {
          case nx: CCStruct if tl != Nil =>
            nx.setFieldTerm(getADTSelector(hd)(rootTerm), setVal, tl)
          case nx: CCStructField if tl != Nil =>
            nx.structs(nx.structName)
              .setFieldTerm(getADTSelector(hd)(rootTerm), setVal, tl)
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
      case Nil =>
        throw new TranslationException(
          "setFieldTerm called " +
            "with" +
            " empty List!")
    }
  }

  def getADTSelector(ind: Int): MonoSortedIFunction = sels(ind)._1

  // Initializes a struct using a stack and returns the initialized term.
  // The stack's top value must be the first term of the struct.
  // The fields are initialized left to right depth-first.
  // If there are not enough values to initialize all the fields, then the
  // remaining fields are initialized to 0.
  def getInitialized(values: Stack[ITerm]): ITerm = {
    val const: IndexedSeq[ITerm] =
      for (field <- sels)
        yield
          field._2 match {
            case CCStructField(name, structs) =>
              structs(name).getInitialized(values)
            case s: CCStruct => s.getInitialized(values)
            case CCHeapPointer(h, _) =>
              if (values.isEmpty) h.nullAddr() else values.pop()
            case CCHeapArrayPointer(h, _, _) =>
              throw new TranslationException(
                "Heap arrays inside structs are" +
                  "not supported.")
              ???
              if (values.isEmpty)
                h.addressRangeCtor(h.nullAddr(), IIntLit(1))
              else values.pop()
            case CCArray(elemTyp,
                         sizeExpr,
                         Some(arraySize),
                         arrayTheory,
                         arrayLocation) => // todo: use arrLoc?
              val initialArrayTerm =
                new SortedConstantTerm(field._1.name, arrayTheory.objSort)
              def arrayBatchStore(arr: ITerm, ind: Int, n: Int): ITerm = {
                if (ind >= n)
                  arr
                else {
                  val innerArr = arrayTheory.store(
                    arr,
                    Int2ITerm(ind),
                    if (values.isEmpty) {
                      if (elemTyp
                            .isInstanceOf[CCArithType]) {
                        IIntLit(0)
                        // todo: use actual
                        //  sorts! need rich
                        //  types here
                      } else {
                        throw new TranslationException("")
                        // todo: this can be
                        //  supported if we
                        //  have access to
                        //   rich types here
                      }
                    } else values.pop()
                  )
                  arrayBatchStore(innerArr, ind + 1, n)
                }
              }
              arrayBatchStore(initialArrayTerm, 0, arraySize)
            case _ =>
              if (values.isEmpty)
                Int2ITerm(0)
              else
                values
                  .pop()
          }
    ctor(const: _*)
  }
}

/**
 * Type for enums that are directly mapped to integers
 */
case class CCIntEnum(name:   String, enumerators: Seq[(String, IdealInt)])
    extends CCType {
  override def toString: String =
    "enum-int " + name + ": (" + enumerators.mkString + ")"
  def shortName = name
}

abstract sealed class CCPointer(typ: CCType) extends CCType {
  def shortName = typ.shortName + "*"
}

case class CCStackPointer(targetInd:    Int,
                          typ:          CCType,
                          fieldAddress: List[Int] = Nil)
    extends CCPointer(typ) {
  override def toString: String =
    typ.shortName +
      " pointer (to: " + targetInd + ")"

}

// todo: how to support heap pointers to adt fields? should we?
// e.g.: what does &(p->x) return when p is a heap pointer?
//       needs to be a Heap.Address along with a way to reach the field
//       maybe another class for this? CCHeapADTFieldPointer...
case class CCHeapPointer(heap: Heap, typ: CCType) extends CCPointer(typ) {
  override def toString: String = typ.shortName + " pointer to heap"
}

/**
 * `Heap`   : arrays allocated via memory allocation functions.
 * `Stack`  : arrays declared on the stack, or allocated via `alloca`.
 * `Global` : global arrays.
 */
object ArrayLocation extends Enumeration {
  type ArrayLocation = Value
  val Global, Stack, Heap = Value
}
import ArrayLocation._
case class CCHeapArrayPointer(heap:          Heap,
                              elementType:   CCType,
                              arrayLocation: ArrayLocation)
    extends CCType {
  def shortName = "[]"
}

// uses the theory of arrays (and not heaps). this is used for InitArray's
// which appear as struct fields (e.g. struct S{int a[4];})
// and for mathematical arrays (then sizeExpr and sizeInt can be None).
case class CCArray(elementType:   CCType, // todo: multidimensional arrays?
                   sizeExpr:      Option[CCExpr],
                   sizeInt:       Option[Int],
                   arrayTheory:   ap.theories.ExtArray,
                   arrayLocation: ArrayLocation)
    extends CCType {
  override def toString: String =
    //typ + "[" + (if (size.nonEmpty) size.get else "") + "]"
    elementType + " array"
  def shortName = elementType + "[]"
}

case object CCClock extends CCType {
  override def toString: String = "clock"
  def shortName = "clock"
}

case object CCDuration extends CCType {
  override def toString: String = "duration"
  def shortName = "duration"
}
