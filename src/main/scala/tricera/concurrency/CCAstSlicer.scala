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

import concurrent_c._
import concurrent_c.Absyn._

import scala.jdk.CollectionConverters._
import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
  ListBuffer}

import tricera.acsl.{Absyn => AcslAst, FoldVisitor => AcslFoldVisitor}
import tricera.acsl.ACSLTranslator

/**
  * Collects C declaration names in ACSL annotations
  */
class ACSLReferencedNamesVisitor extends AcslFoldVisitor[Set[String], Unit] {
  override def leaf(arg: Unit): Set[String] = Set.empty
  override def combine(x: Set[String], y: Set[String], arg: Unit): Set[String] =
    x ++ y

  override def visit(e: AcslAst.EIdent, arg: Unit): Set[String] = Set(e.id_)
  override def visit(e: AcslAst.EApplication, arg: Unit): Set[String] =
    Set(e.id_) ++ super.visit(e, arg)
  override def visit(t: AcslAst.Tcollection, arg: Unit): Set[String] = Set(t.id_)
}

/**
  * Collect referenced names in the C and ACSL AST (e.g., for slicing).
  */
class CCAstCollectReferencedNamesVisitor
    extends FoldVisitor[Set[String], Unit] {
  private val acslRefs = new ACSLReferencedNamesVisitor

  def apply(decl: External_declaration): Set[String] = decl.accept(this, ())

  override def leaf(arg: Unit): Set[String] = Set.empty
  override def combine(x: Set[String], y: Set[String], arg: Unit): Set[String] =
    x ++ y

  override def visit(exp: Evar, arg: Unit): Set[String] = Set(exp.cident_)
  override def visit(exp: EvarWithType, arg: Unit): Set[String] =
    Set(exp.cident_) ++ super.visit(exp, arg)

  override def visit(spec: TagType, arg: Unit): Set[String] = Set(spec.cident_)
  override def visit(spec: EnumVar, arg: Unit): Set[String] = Set(spec.cident_)

  // ACSL annotations
  override def visit(annot: Annot1, arg: Unit): Set[String] = {
    val marker = tricera.Literals.annotationMarker.length
    val text   = annot.annotationstring_
    val body   =
      if (text.length >= 2 * marker) text.substring(marker, text.length - marker)
      else text
    try ACSLTranslator.parseToAST("/*@" + body + "*/").accept(acslRefs, ())
    catch { case _: Throwable => Set.empty }
  }

  // global predicate definitions carry their annotation as a raw string
  override def visit(ext: PredicateExternal, arg: Unit): Set[String] = {
    val body = ext.predicatestring_
      .stripPrefix(tricera.Literals.predicateOpenMarker)
      .stripSuffix(tricera.Literals.predicateCloseMarker)
    try ACSLTranslator.parseToAST("/*@" + body + "*/").accept(acslRefs, ())
    catch { case _: Throwable => Set.empty }
  }
}

/**
  * Slice dead code. Reachability starts at the entry function (-m),
  * only removes what it can prove unused.
  */
object CCAstSlicer {
  private val getName     = new CCAstGetNameVistor
  private val collectRefs = new CCAstCollectReferencedNamesVisitor

  def apply(program: Program, entryFunction: String): Program = {
    val progr = program.asInstanceOf[Progr]
    val decls = progr.listexternal_declaration_.asScala.toList

    val sliceable = decls.filter(isSliceable)
    val namesOf: Map[External_declaration, Set[String]] =
      sliceable.map(d => d -> declaredNames(d)).toMap

    def mustKeep(d: External_declaration): Boolean =
      !isSliceable(d) || (namesOf(d).isEmpty && !declaresNothing(d))

    val declsByName = new MHashMap[String, ListBuffer[External_declaration]]
    for (d <- sliceable; n <- namesOf(d))
      declsByName.getOrElseUpdate(n, new ListBuffer) += d

    val reachable = new MHashSet[String]
    val worklist  = new ListBuffer[String]
    val expanded  = new MHashSet[External_declaration]

    def addName(n: String): Unit =
      if (!reachable(n)) { reachable += n; worklist += n }

    // expand kept declarations so that they cannot refer to a dropped one
    def expand(d: External_declaration): Unit =
      if (!expanded(d)) { expanded += d; collectRefs(d).foreach(addName) }

    addName(entryFunction)
    for (d <- decls if mustKeep(d)) expand(d)
    for (d <- sliceable if isAnnotatedFunc(d)) {
      namesOf(d).foreach(addName)
      expand(d)
    }
    while (worklist.nonEmpty) {
      val n = worklist.remove(0)
      for (d <- declsByName.getOrElse(n, Nil)) expand(d)
    }

    val kept = decls.filter(d => mustKeep(d) || namesOf(d).exists(reachable))

    // don't remove this, used in slicer regression tests
    tricera.Util.printlnDebug("slice removed " + (decls.size - kept.size) +
      " of " + decls.size + " declarations: " +
      decls.filterNot(kept.toSet).flatMap(d =>
        namesOf.getOrElse(d, Set.empty)).mkString(", "))

    val newList = new ListExternal_declaration
    newList.addAll(kept.asJava)
    new Progr(newList)
  }

  private def isSliceable(ext: External_declaration): Boolean = ext match {
    case _: Afunc => true
    case g: Global => g.dec_ match {
      case _: Declarators  => true
      case _: NoDeclarator => true
      case _ => false // predicate declarations
    }
    case _ => false // threads, channels, ignored
  }

  // Empty anon struct or union => always dead
  private def declaresNothing(ext: External_declaration): Boolean = ext match {
    case g: Global => g.dec_ match {
      case d: NoDeclarator => d.listdeclaration_specifier_.asScala.exists {
        case t: Type => t.type_specifier_ match {
          case s: Tstruct => s.struct_or_union_spec_.isInstanceOf[Unique]
          case _ => false
        }
        case _ => false
      }
      case _ => false
    }
    case _ => false
  }

  // A function whose definition carries an ACSL annotation is verified
  // independently of any call site, so it must stay live.
  private def isAnnotatedFunc(ext: External_declaration): Boolean = ext match {
    case f: Afunc => f.function_def_ match {
      case d: AnnotatedFunc => !d.listannotation_.isEmpty
      case d: NewFuncInt    => !d.listannotation_.isEmpty
      case _: NewFunc       => false
    }
    case _ => false
  }

  private def declaredNames(ext: External_declaration): Set[String] = ext match {
    case f: Afunc =>
      try Set(f.accept(getName, ())) catch { case _: Throwable => Set.empty }
    case g: Global => g.dec_ match {
      case d: Declarators =>
        declaratorNames(d.listinit_declarator_) ++
          typeDefNames(d.listdeclaration_specifier_)
      case d: NoDeclarator => typeDefNames(d.listdeclaration_specifier_)
      case _ => Set.empty
    }
    case _ => Set.empty
  }

  private def declaratorNames(inits: ListInit_declarator): Set[String] =
    try inits.asScala.map(_.accept(getName, ())).filter(_.nonEmpty).toSet
    catch { case _: Throwable => Set.empty }

  // The tags and constants introduced by struct/union/enum
  private def typeDefNames(specs: ListDeclaration_specifier): Set[String] =
    specs.asScala.flatMap {
      case t: Type => t.type_specifier_ match {
        case s: Tstruct => s.struct_or_union_spec_ match {
          case tag: Tag => Set(tag.cident_)
          case _ => Set.empty[String]
        }
        case e: Tenum => e.enum_specifier_ match {
          case named: EnumName =>
            Set(named.cident_) ++ enumeratorNames(named.listenumerator_)
          case anon: EnumDec => enumeratorNames(anon.listenumerator_)
          case _ => Set.empty[String]
        }
        case _ => Set.empty[String]
      }
      case _ => Set.empty[String]
    }.toSet

  private def enumeratorNames(l: ListEnumerator): Set[String] =
    l.asScala.map {
      case p: Plain    => p.cident_
      case e: EnumInit => e.cident_
    }.toSet
}
