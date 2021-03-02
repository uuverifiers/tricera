package tricera.benchmarking

object Benchmarking {
  // Execution Results
  sealed trait ExecutionError
  sealed abstract class ExecutionResult {
    def toString : String
  }
  case object ParseError extends ExecutionResult with ExecutionError {
    override def toString : String =
      "input could not be parsed"
  }
  case object ArrayError extends ExecutionResult with ExecutionError  {
    override def toString : String =
      "input file contains arrays"
  }
  case object OutOfMemory extends ExecutionResult with ExecutionError  {
    override def toString : String =
      "ran out of memory"
  }
  case object StackOverflow extends ExecutionResult with ExecutionError  {
    override def toString : String =
      "stack overflow"
  }
  case class OtherError (e : String) extends ExecutionResult with ExecutionError {
    override def toString : String =
      "other error: " + e
  }
  case object Timeout extends ExecutionResult with ExecutionError {
    override def toString : String =
      "timeout"
  }
  case object Safe extends ExecutionResult {
    override def toString : String =
      "safe"
  }
  case object Unsafe extends ExecutionResult {
    override def toString : String =
      "unsafe"
  }
  case object DidNotExecute extends ExecutionResult {
    override def toString : String =
      "did not execute"
  }

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
                                trackResult : List[(BenchmarkTrack, Boolean)] = Nil,
                                modelledHeap : Boolean = false, // true if the bm contained heap operations
                                elapsedTime  : Double = 0,
                                preprocessTime : Double = 0
                              )

  class Timer {
    private var stopped = true
    private var startTime : Double = System.nanoTime()
    private var stopDuration  : Double = 0

    def pause() { stopped = true; stopDuration = System.nanoTime() - startTime }
    def stop()  { stopped = true; stopDuration = System.nanoTime() - startTime }
    def start() { stopped = false; startTime = System.nanoTime() }

    def s  : Double = ns / 1e9d
    def ms : Double = ns / 1e6d
    def us : Double = ns / 1e3d
    def ns : Double =
      if (stopped) stopDuration else System.nanoTime() - startTime
  }

}