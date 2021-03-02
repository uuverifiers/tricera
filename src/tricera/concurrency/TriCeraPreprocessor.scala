package tricera.concurrency

import com.sun.jna._

trait TriCeraPreprocessor extends Library {
  def _Z7runTooliPPKcS0_(argc : Int, argv : Array[String],
                         outputFileAbsolutePath : String) : PreprocessOutput
}

object TriCeraPreprocessor {
  private var _tp : TriCeraPreprocessor = _

  def run() : TriCeraPreprocessor = {
    if ( _tp == null ) {
      NativeLibrary.addSearchPath("tricera-preprocessor", "lib")
      NativeLibrary.addSearchPath("tricera-preprocessor", "dist")
      NativeLibrary.addSearchPath("tricera-preprocessor", "preprocessor/build")
      Native.DEBUG_JNA_LOAD=true;
      _tp = Native.loadLibrary("tricera-preprocessor",
        classOf[TriCeraPreprocessor]).asInstanceOf[TriCeraPreprocessor]
      // todo: error handling if cannot find library? maybe run without pp
    }
    _tp
  }
}
