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

package tricera.acsl

import tricera.acsl.{Absyn => AST, SourceInfoProvider}
import scala.jdk.CollectionConverters._

object ACSLRewriter {

  trait Rule {
    type Arg
    def visitor : ComposVisitor[Arg]
    def arg     : Arg
  }

  def rewrite(annot : AST.Annotation, rule : Rule) : AST.Annotation =
    annot.accept(rule.visitor, rule.arg)

  // paramToGlobal: parameter name -> replacing global's name
  def globalizeParams(paramToGlobal : Map[String, String]) : Rule = new Rule {
    type Arg = Map[String, String]
    val visitor = new ParamToGlobalVisitor
    val arg     = paramToGlobal
  }

  private class ParamToGlobalVisitor extends ComposVisitor[Map[String, String]] {
    private def at[N <: SourceInfoProvider](src : SourceInfoProvider, node : N) : N = {
      node.setLineNum(src.getLineNum)
      node.setColNum(src.getColNum)
      node.setOffset(src.getOffset)
      node
    }

    override def visit(p : AST.EUnary, m : Map[String, String]) : AST.Expr =
      p.unaryop_ match {
        case _ : AST.UnaryPtrDeref =>
          globalizedBase(p.expr_, m) match {
            case Some(g) => at(p, new AST.EIdent(g))
            case None    => super.visit(p, m)
          }
        case _ => super.visit(p, m)
      }

    override def visit(p : AST.EStructPtrFieldAccess,
                       m : Map[String, String]) : AST.Expr =
      globalizedBase(p.expr_, m) match {
        case Some(g) =>
          at(p, new AST.EStructFieldAccess(at(p, new AST.EIdent(g)), p.id_))
        case None => super.visit(p, m)
      }

    override def visit(p : AST.EIdent, m : Map[String, String]) : AST.Expr =
      if (m.contains(p.id_))
        at(p, new AST.EUnary(at(p, new AST.UnaryAddressOf()),
                             at(p, new AST.EIdent(m(p.id_)))))
      else super.visit(p, m)

    override def visit(p : AST.EValid, m : Map[String, String]) : AST.Expr =
      rewriteValid(p, p.listlocation_, m, ls => at(p, new AST.EValid(ls)))

    override def visit(p : AST.EValidRead, m : Map[String, String]) : AST.Expr =
      rewriteValid(p, p.listlocation_, m, ls => at(p, new AST.EValidRead(ls)))

    private def rewriteValid(src     : SourceInfoProvider,
                             locs    : AST.ListLocation,
                             m       : Map[String, String],
                             rebuild : AST.ListLocation => AST.Expr) : AST.Expr = {
      val kept = locs.asScala.filterNot(isGlobalizedLocation(_, m))
      if (kept.isEmpty) at(src, new AST.ELit(at(src, new AST.LitTrue())))
      else {
        val out = new AST.ListLocation()
        kept.foreach(l => out.add(l.accept(this, m).asInstanceOf[AST.Location]))
        rebuild(out)
      }
    }

    private def isGlobalizedLocation(loc : AST.Location,
                                     m   : Map[String, String]) : Boolean =
      loc match {
        case al : AST.ALocation => al.tset_ match {
          case ts : AST.TSetTerm => baseName(ts.expr_).exists(m.contains)
          case _ => false
        }
        case _ => false
      }

    private def baseName(e : AST.Expr) : Option[String] = e match {
      case old : AST.EOld   => baseName(old.expr_)
      case id  : AST.EIdent => Some(id.id_)
      case _                => None
    }

    private def globalizedBase(e : AST.Expr,
                               m : Map[String, String]) : Option[String] =
      baseName(e).filter(m.contains).map(m)
  }
}
