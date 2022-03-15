package tricera.parsers

import ap.parser.Parser2InputAbsy.CRRemover2
import tricera.concurrency.CCReader.ParseException
import tricera.concurrency.concurrent_c
import tricera.concurrency.concurrent_c.Absyn.{Afunc, Exp, ExprS, NewFunc, Progr, ScompTwo, SexprTwo}
import tricera.concurrency.concurrent_c.{Yylex, parser}

object ParserUtil {
  def parseWithEntry[T](input : java.io.Reader,
                        entry : (parser) => T) : T = {
    val l = new Yylex(new CRRemover2 (input))
    val p = new parser(l, l.getSymbolFactory)

    try { entry(p) } catch {
      case e : Exception =>
        throw new ParseException(
          "At line " + String.valueOf(l.line_num()) +
            ", near \"" + l.buff() + "\" :" +
            "     " + e.getMessage())
    }
  }

  // parses the expression in programs of the form:
  // void foo() { expression ; }
  // this is done to overcome java-cup's limitation of a single entry point
  private def parseExpFromProg(input : java.io.Reader) : Exp = {
    def entry(parser : concurrent_c.parser) = {
      val parseTree = parser.pProgram
      try {
        parseTree.asInstanceOf[Progr].listexternal_declaration_.getFirst.
          asInstanceOf[Afunc].function_def_.asInstanceOf[NewFunc].
          compound_stm_.asInstanceOf[ScompTwo].liststm_.getFirst.
          asInstanceOf[ExprS].expression_stm_.asInstanceOf[SexprTwo].exp_
      } catch {
        case _ : Exception => throw new ParseException(
          "Input is not of the form: void foo() { expression ; }")
      }
    }
    parseWithEntry(input, entry _)
  }

  def parseExp(exp : String) : Exp = {
    parseExpFromProg(
      new java.io.BufferedReader (
        new java.io.StringReader("void foo () { "  + exp + "; }"))
    )
  }
}
