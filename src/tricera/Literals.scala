package tricera

/**
  * This object is intended to collect literal constants
  * that are needed in more than one place throughout
  * the application. The number of these should be kept
  * at a minimum.
  */
object Literals {
  // Used for signaling the context of a predicate variable value.
  val preExecSuffix = "_old"
  val postExecSuffix = "_post"
  val resultExecSuffix = "_res"
  val invPrefix = "inv_"

  // Used for context of predicates
  val predPostSuffix = "_post"
  val predPreSuffix = "_pre"

  // Used for indicating that an annotation is ACSL related
  val annotationMarker = "■■" // ascii 254 times 2
}
