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

  // Used for indicating that an annotation is ACSL related. Two
  // markers so the C grammar can tell hint/contract annotations apart
  // from standalone ones (ghost declarations/statements).
  val annotationMarker = "■■"
  val standaloneAnnotationMarker = "●●"

  val atExpressionName = "$at"

  val anonStructName = ".AS"
  val anonEnumName   = ".ES"
}
