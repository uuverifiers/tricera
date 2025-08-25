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

package tricera.concurrency

import concurrent_c._
import concurrent_c.Absyn._
import tricera.Literals.atExpressionName
import scala.collection.mutable.{HashMap => MHashMap, ListBuffer}
import scala.collection.JavaConverters._

/**
 * A two-pass transformer for handling `at(label, expr)` expressions.
 *
 * 1. Collection Pass: The AST is traversed to find all labeled statements and
 *    all calls to the `at` function. The information is collected into an
 *    `AtCallCollectionResult`.
 * 2. Transformation Pass: Based on the collected information, the transformer
 *    a) injects a new "ghost" variable declaration just before each relevant
 *       label, initialized with the expression from the `at` call,
 *    b) replaces the original `at(label, expr)` call with a reference to the
 *       newly created ghost variable.
 */
object CCAstAtExpressionTransformer {
  /**
   * Class to hold information about a discovered `at(...)` call.
   */
  private case class AtCallInfo(
    label             : String,
    typeName          : Type_name,
    expr              : Exp,
    call              : Efunkpar,
    enclosingFunction : Function_def
  )

  /**
   * Class to hold the results of the collection phase.
   * @param atCalls     A sequence of all `at(...)` calls found.
   * @param labeledStms A map from label names to the function and statement node.
   */
  private case class AtCallCollectionResult(
    atCalls     : Seq[AtCallInfo],
    labeledStms : Map[String, (Function_def, SlabelOne)]
  )

  private val copyVisitor = new CCAstCopyVisitor()

  def transform(program : Program) : Program = {
    val collectionResult = collectLabelsAndAtCalls(program)
    if (collectionResult.atCalls.isEmpty)
      return program

    val (replacements, insertions) = planTransformations(collectionResult)

    val transformer = new AtTransformer(replacements, insertions)
    program.accept(transformer, ())
  }

  /**
   * Helper to find labels and `at(...)` calls in the program.
   */
  private def collectLabelsAndAtCalls(program : Program) : AtCallCollectionResult = {
    val atCallsBuffer = new ListBuffer[AtCallInfo]
    val labelMap = new MHashMap[String, (Function_def, SlabelOne)]

    val collector = new LabelAndAtCallCollector(atCallsBuffer, labelMap)
    program.accept(collector, null)

    AtCallCollectionResult(atCallsBuffer.toList, labelMap.toMap)
  }

  private class LabelAndAtCallCollector(
    val atCallsBuffer   : ListBuffer[AtCallInfo],
    val labelToLocation : MHashMap[String, (Function_def, SlabelOne)]
  ) extends ComposVisitor[Function_def] {
    private val getName = new CCAstGetNameVistor

    override def visit(p : Afunc, arg : Function_def) : Afunc = {
      super.visit(p, p.function_def_)
      p
    }

    override def visit(p : SlabelOne, currentFunc : Function_def) : SlabelOne = {
      if (currentFunc != null) {
        if (labelToLocation.contains(p.cident_))
          println(s"Warning: Duplicate label '${p.cident_}' found.")
        labelToLocation.put(p.cident_, (currentFunc, p))
      }
      super.visit(p, currentFunc)
      p
    }

    override def visit(p : Efunkpar, currentFunc : Function_def) : Efunkpar = {
      val funcName = p.accept(getName, ())
      if (funcName == atExpressionName) {
        if (currentFunc != null && p.listexp_.size() == 2) {
          val labelArg = p.listexp_.get(0)
          val expressionArg = p.listexp_.get(1)

          expressionArg match {
            case typecast: Etypeconv =>
              val label = labelArg.accept(getName, ())
              val typeName = typecast.type_name_
              val innerExpr = typecast.exp_
              atCallsBuffer += AtCallInfo(label, typeName, innerExpr, p, currentFunc)
            case _ =>
              throw new IllegalArgumentException(
                s"${tricera.Util.getLineString(p)}: " +
                s"The second argument to $atExpressionName must be a typecast " +
                s"of the form (Type)(expr).")
          }
        } else if (p.listexp_.size() != 2)
          throw new IllegalArgumentException(
            s"${tricera.Util.getLineString(p)}: " +
            s"Malformed $atExpressionName call with " +
            s"${p.listexp_.size()} arguments.")
      }
      super.visit(p, currentFunc)
      p
    }
  }

  /**
   * Figure out which at calls to replace and what to add to label sites
   */
  private def planTransformations(collection : AtCallCollectionResult) :
  (Map[Efunkpar, Evar], Map[SlabelOne, Seq[Stm]]) = {

    val replacements = new MHashMap[Efunkpar, Evar]
    val insertions = new MHashMap[SlabelOne, ListBuffer[Stm]]
    collection.labeledStms.values.foreach { case (_, label) =>
      insertions.put(label, new ListBuffer[Stm]()) }
    val labelCounters = new MHashMap[String, Int].withDefaultValue(0)

    for (atCall <- collection.atCalls) {
      collection.labeledStms.get(atCall.label) match {
        case Some((funcDef, slabelNode)) if funcDef eq atCall.enclosingFunction =>
          val counter = labelCounters(atCall.label)
          val ghostVarName = s"${atExpressionName}_${atCall.label}_$counter"
          labelCounters(atCall.label) = counter + 1

          val newStatement =
            buildDeclarationStatement(ghostVarName, atCall.typeName, atCall.expr)
          insertions(slabelNode) += newStatement

          val replacementVar = new Evar(ghostVarName)
          replacements.put(atCall.call, replacementVar)
        case _ =>
      }
    }
    (replacements.toMap, insertions.mapValues(_.toList).toMap)
  }

  private def buildDeclarationStatement(varName  : String,
                                        T        : Type_name,
                                        initExpr : Exp) : Stm = {
    val copiedExpr = initExpr.accept(copyVisitor, ())
    val initializer = new InitExpr(copiedExpr)

    val directDeclarator = new Name(varName)
    val declarator = new NoPointer(directDeclarator)
    val initDeclarator = new InitDecl(declarator, initializer)
    val listInitDeclarator = new ListInit_declarator()
    listInitDeclarator.add(initDeclarator)

    val specQuals = T match {
      case pt: PlainType    => pt.listspec_qual_
      case et: ExtendedType => et.listspec_qual_
    }

    val listDeclSpec = new ListDeclaration_specifier
    specQuals.asScala.foreach {
      case sq: TypeSpec => listDeclSpec.add(new Type(sq.type_specifier_))
      case sq: QualSpec => listDeclSpec.add(new SpecProp(sq.type_qualifier_))
    }

    val dec = new Declarators(
      listDeclSpec, listInitDeclarator, new ListExtra_specifier())
    new DecS(dec)
  }

  /**
   * A visitor that applies the planned transformations to the AST.
   */
  private class AtTransformer(
    replacements: Map[Efunkpar, Evar],
    insertions: Map[SlabelOne, Seq[Stm]]
  ) extends CCAstCopyWithLocation[Unit] {

    /**
     * Replaces an `at(...)` call with its corresponding ghost variable.
     */
    override def visit(p : Efunkpar, arg : Unit) : Exp = {
      replacements.get(p) match {
        case Some(replacementVar) =>
          copyLocationInformation(p, new Evar(replacementVar.cident_))
        case None => super.visit(p, arg)
      }
    }

    /**
     * Inserts ghost var declarations before their corresponding labels.
     */
    override def visit(p : ScompTwo, arg : Unit) : Compound_stm = {
      val newStatements = new ListStm()
      for (originalStm <- p.liststm_.asScala) {
        originalStm match {
          case ls: LabelS => ls.labeled_stm_ match {
            case slabel : SlabelOne =>
              insertions.get(slabel).foreach { stmtsToInsert =>
                newStatements.addAll(stmtsToInsert.asJavaCollection)
              }
            case _ => // other label types
          }
          case _ => // not a label
        }
        newStatements.add(originalStm.accept(this, arg))
      }
      val newCompStm = new ScompTwo(newStatements)
      copyLocationInformation(p, newCompStm)
    }
  }
}
