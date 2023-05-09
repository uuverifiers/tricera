package tricera.postprocessor

import ap.parser._
import ap.terfor.ConstantTerm
import IExpression._

object ACSLExpression extends ContractConditionTools {
  val valid = new Predicate("valid", 1)
  val deref = new IFunction("deref", 1, false, false) // *p
  val oldDeref = new IFunction("oldDeref", 1, false, false) // \old(*p)
  val derefOld = new IFunction("derefOld", 1, false, false) // *\old(p)

  // Here a ConstantTerm is introduced as a container for the variable name
  def derefFunApp(
      function: IFunction,
      variable: ISortedVariable,
      quantifierDepth: Int,
      acslArgNames: Seq[String]
  ) = {
    val name = stripOld(getVarName(variable, quantifierDepth, acslArgNames))
    IFunApp(function, Seq(IConstant(new ConstantTerm(name))))
  }
}
