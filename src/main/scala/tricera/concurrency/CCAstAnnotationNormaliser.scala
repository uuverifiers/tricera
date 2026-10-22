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

/**
 * Rewrites the parser-only statement forms AnnotatedS and
 * BlockEndAnnotationsS into AnnotationS and AnnotatedIterS.
 *
 * In the grammar, a code annotation is read together with the statement after
 * it, so that an annotation in front of an if branch or a loop body belongs to
 * that branch or body. In the rest of the translation, annotations are
 * statements of their own, and building that shape during parsing would make
 * the grammar ambiguous, so the shape is restored here.
 * In a statement list, the annotation is followed by its statement, and where
 * a single statement is expected, both are put into a new block. An annotation
 * directly before a loop stays attached to the loop.
 */
object CCAstAnnotationNormaliser {
  def transform(program : Program) : Program =
    program.accept(new AnnotationNormaliser, ())

  private class AnnotationNormaliser
    extends ComposVisitor[Unit] with CopyAstLocation {

    override def visit(p : ScompTwo, arg : Unit) : Compound_stm =
      copyLocationInformation(p, new ScompTwo(blockItemList(p.liststm_)))

    override def visit(p : GhostStm, arg : Unit) : Stm =
      copyLocationInformation(p, new GhostStm(blockItemList(p.liststm_)))

    override def visit(p : LabelS, arg : Unit) : Stm = singleStatement(p)

    override def visit(p : AnnotatedS, arg : Unit) : Stm = singleStatement(p)

    private def singleStatement(stm : Stm) : Stm = blockItems(stm) match {
      case Seq(item) => item
      case items =>
        val block = new ScompTwo(statementList(items))
        copyLocationInformation[SourceInfoProvider](stm, block)
        copyLocationInformation(stm, new CompS(block))
    }

    private def blockItemList(stms : ListStm) : ListStm =
      statementList(stms.asScala.toSeq.flatMap(blockItems))

    private def blockItems(stm : Stm) : Seq[Stm] = stm match {
      case annotated : AnnotatedS => annotated.stm_ match {
        case loop : IterS =>
          Seq(copyLocationInformation(annotated, new AnnotatedIterS(
            annotated.annotation_.accept(this, ()),
            loop.iter_stm_.accept(this, ()))))
        case next =>
          annotationStatement(annotated.annotation_) +: blockItems(next)
      }
      case annotations : BlockEndAnnotationsS =>
        annotations.listannotation_.asScala.toSeq.map(annotationStatement)
      case labelled : LabelS =>
        val (label, rest) = labelItems(labelled.labeled_stm_)
        copyLocationInformation(labelled, new LabelS(label)) +: rest
      case _ =>
        Seq(stm.accept(this, ()))
    }

    private def labelItems(label : Labeled_stm) : (Labeled_stm, Seq[Stm]) = {
      def labelFirstItem(stm : Stm, labelWith : Stm => Labeled_stm) = {
        val items = blockItems(stm)
        (copyLocationInformation(label, labelWith(items.head)), items.tail)
      }
      label match {
        case l : SlabelOne =>
          labelFirstItem(l.stm_, new SlabelOne(l.cident_, _))
        case l : SlabelTwo =>
          labelFirstItem(l.stm_, new SlabelTwo(
            l.constant_expression_.accept(this, ()), _))
        case l : SlabelThree =>
          labelFirstItem(l.stm_, new SlabelThree(_))
      }
    }

    private def annotationStatement(annotation : Annotation) : Stm = {
      val stm = new AnnotationS(annotation.accept(this, ()))
      copyLocationInformation[SourceInfoProvider](annotation, stm)
      stm
    }

    private def statementList(stms : Seq[Stm]) : ListStm = {
      val list = new ListStm
      list.addAll(stms.asJava)
      list
    }
  }
}
