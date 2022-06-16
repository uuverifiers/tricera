package tricera.concurrency

import tricera.concurrency.concurrent_c.Absyn.{Dec, Global, Progr}

object Util {
  def parseGlobalDeclaration(input : java.io.Reader) : Dec = {
    def entry(parser : concurrent_c.parser) = {
      val parseTree = parser.pProgram()
      parseTree match {
        case p : Progr if p.listexternal_declaration_.size == 1 =>
          p.listexternal_declaration_.getFirst match {
            case global : Global => global.dec_
            case _ =>
              throw new Exception(
                "Input is not a global declaration")
          }
        case _ => throw new Exception(
          "Input is not a global declaration")
      }
    }
    CCReader.parseWithEntry(input, entry)
  }
}
