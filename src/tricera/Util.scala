package tricera
import tricera.concurrency.ccreader.Vars.SourceInfo
import tricera.concurrency.concurrent_c.Absyn._

object Util {
  def warn(msg : String) : Unit =
    Console.err.println("Warning: " + msg)

  // todo: is below really the only way to get line numbers?
  def getSourceInfo(exp: Exp): SourceInfo = exp match {
    case exp: Ecomma => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eassign => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Econdition => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Elor => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eland => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebitor => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebitexor => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebitand => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eeq => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eneq => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Elthen => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Egrthen => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ele => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ege => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eleft => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eright => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eplus => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eminus => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Etimes => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ediv => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Emod => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Etypeconv => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epreinc => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epredec => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epreop => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebytesexpr => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Ebytestype => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Earray => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Efunk => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Efunkpar => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Eselect => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epoint => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epostinc => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Epostdec => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Evar => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Econst => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Estring => SourceInfo(exp.line_num, exp.col_num, exp.offset)
    case exp: Enondet => SourceInfo(exp.line_num, exp.col_num, exp.offset)
  }

  def getLineString(exp: Exp): String = {
    val sourceInfo = getSourceInfo(exp)
    "At line " + sourceInfo.line + " (offset " + sourceInfo.offset + "): "
  }
}