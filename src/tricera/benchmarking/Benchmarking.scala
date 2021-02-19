package tricera.benchmarking

object Benchmarking {
  // Execution Results
  sealed trait ExecutionResult
  case object ParseError extends ExecutionResult // input could not be parsed
  case object ArrayError extends ExecutionResult // input contains arrays
  case object OutOfMemory extends ExecutionResult
  case object StackOverflow extends ExecutionResult
  case class OtherError (e : String) extends ExecutionResult
  case object Timeout extends ExecutionResult
  case object Safe extends ExecutionResult
  case object Unsafe extends ExecutionResult
  case object DidNotExecute extends ExecutionResult

  // SV-COMP related, should probably move somewhere else...
  // supported SV-COMP benchmark tracks
  sealed trait BenchmarkTrack
  case object Reachability extends BenchmarkTrack { // unreachability of error
    override def toString : String = "unreach-call"
  }
  // no subtracks need to be provided on a pass, a single subtrack is provided
  // on fail
  case class MemSafety(subTrack : Option[MemSubTrack]) extends BenchmarkTrack {
    override def toString : String =
      "valid-memsafety" + (subTrack match {
        case Some(t) => "/" + t.toString
        case None => ""
      })
  }
  sealed trait MemSubTrack
  case object MemTrack extends MemSubTrack { // valid-memtrack
    override def toString : String = "valid-memtrack"
  }
  case object ValidDeref extends MemSubTrack { // valid-deref
    override def toString : String = "valid-deref"
  }
  case object ValidFree extends MemSubTrack { // valid-free
    override def toString : String = "valid-free"
  }

  // returned by Main
  case class ExecutionSummary (
                                executionResult: ExecutionResult,
                                // if a supported SV-COMP track is provided, returns a list of these tracks
                                // and whether the execution result matched the expected verdict or not
                                trackResult : List[(BenchmarkTrack, Boolean)],
                                modelledHeap : Boolean // true if the bm contained heap operations
                              )
}
