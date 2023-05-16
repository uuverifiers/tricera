package tricera.postprocessor

object ContractConditionType extends Enumeration {
  type ContractConditionType = Value
  val Precondition, Postcondition = Value
}

import ContractConditionType._