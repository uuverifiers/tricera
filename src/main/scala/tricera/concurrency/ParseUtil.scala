package tricera.concurrency

import tricera.concurrency.ccreader.CCExceptions
import tricera.concurrency.concurrent_c.Absyn._

import java.io.{Reader, StringReader}

object ParseUtil {
  def parseGlobalDeclaration(input : Reader) : Dec = {
    def entry(parser : concurrent_c.parser) = {
      val parseTree = parser.pProgram()
      parseTree match {
        case p : Progr if p.listexternal_declaration_.size == 1 =>
          p.listexternal_declaration_.getFirst match {
            case global : Global => global.dec_
            case _ => throw new Exception("Input is not a global declaration")
          }
        case _ => throw new Exception(
          "Input is not a global declaration")
      }
    }
    CCReader.parseWithEntry(input, entry)
  }

  def parseFunctionDefinition(input: Reader): External_declaration = {
    def entry(parser: concurrent_c.parser) = {
      val parseTree = parser.pProgram()
      parseTree match {
        case p: Progr if p.listexternal_declaration_.size == 1 =>
          p.listexternal_declaration_.getFirst match {
            case f: Afunc => f
            case _ => throw new Exception("Input is not a function definition")
          }
        case _ => throw new Exception("Input is not a function definition")
      }
    }
    CCReader.parseWithEntry(input, entry)
  }

  def parseStatement(input: java.io.Reader): Stm = {
    val statementText = new java.util.Scanner(input).useDelimiter("\\A").next()

    val programText = s"void dummy() { $statementText }"
    val programReader = new java.io.StringReader(programText)

    def entry(parser: concurrent_c.parser): Stm = {
      val programAst = parser.pProgram()
      programAst match {
        case p: Progr =>
          val funcExtDecl = p.listexternal_declaration_.getFirst.asInstanceOf[Afunc]
          val funcDef = funcExtDecl.function_def_
          val body = CCReader.FuncDef(funcDef).body.asInstanceOf[ScompTwo]

          if (body.liststm_.size != 1) {
            throw new Exception(
              s"Internal parser error: Expected to parse one statement, but found ${body.liststm_.size}. " +
              s"Original text: '$statementText'")
          }
          body.liststm_.getFirst

        case _ =>
          throw new Exception(s"Internal parser error: Could not parse wrapped statement: '$statementText'")
      }
    }

    try {
      CCReader.parseWithEntry(programReader, entry)
    } catch {
      case e: Exception =>
        throw new CCExceptions.ParseException(
          s"Failed to parse statement string: '$statementText'. Reason: ${e.getMessage}")
    }
  }

  def parseExpression(input: java.io.Reader): Exp = {
    val expressionText = new java.util.Scanner(input).useDelimiter("\\A").next()
    // Wrap in a dummy function and extract.
    val programText = s"void __dummy_func() { ($expressionText); }"

    def entry(parser: concurrent_c.parser): Exp = {
      parser.pProgram() match {
        case p: Progr =>
          val func = p.listexternal_declaration_.getFirst.asInstanceOf[Afunc].function_def_
          val body = CCReader.FuncDef(func).body.asInstanceOf[ScompTwo]
          val stmt = body.liststm_.getFirst.asInstanceOf[ExprS]
          stmt.expression_stm_.asInstanceOf[SexprTwo].exp_
      }
    }
    CCReader.parseWithEntry(new StringReader(programText), entry)
  }

}
