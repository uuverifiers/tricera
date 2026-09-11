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

  // Used for indicating that an annotation is ACSL related.
  val annotationMarker = "■■"

  // Bracket markers emitted by `CommentPreprocessor` around ghost comments
  val ghostOpenMarker  = "⟦"
  val ghostCloseMarker = "⟧"

  // Markers around standalone global annotations (e.g. predicate definitions)
  val predicateOpenMarker  = "⟪"
  val predicateCloseMarker = "⟫"

  val atExpressionName = "$at"

  // Prefix for variables holding a value captured at a labelled program state
  // (\at(e, label)).
  val captureVarPrefix = "$cap_"

  val anonStructName = ".AS"
  val anonEnumName   = ".ES"
}
