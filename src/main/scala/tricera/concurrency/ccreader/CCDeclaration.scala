package tricera.concurrency.ccreader

import tricera.Util.SourceInfo
import tricera.concurrency.concurrent_c.Absyn._

sealed abstract class CCDeclaration
// todo: better handling of function declarations
case class CCFunctionDeclaration(name        : String,
                                 typ         : CCType,
                                 directDecl  : Direct_declarator,
                                 srcInfo     : SourceInfo) extends CCDeclaration
case class CCVarDeclaration(name             : String,
                            typ              : CCType,
                            maybeInitializer : Option[Initializer],
                            hints            : Seq[Annotation],
                            isArray          : Boolean,
                            isStatic         : Boolean,
                            needsHeap        : Boolean,
                            initArrayExpr    : Option[Constant_expression],
                            srcInfo          : SourceInfo) extends CCDeclaration
case object CCNoDeclaration extends CCDeclaration
case class CCPredDeclaration(predHints : ListPred_hint,
                             srcInfo   : SourceInfo) extends CCDeclaration

case class CCInterpPredDeclaration(predDecl: Pred_interp) extends CCDeclaration
