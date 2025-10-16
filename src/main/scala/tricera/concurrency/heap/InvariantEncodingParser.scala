package tricera.concurrency.heap

import tricera.concurrency.ccreader.CCExceptions.TranslationException
import net.jcazevedo.moultingyaml._

object InvariantEncodingParser {
  case class Declaration(name          : String,
                         `type`        : String,
                         initial_value : Option[String])
  case class Argument   (name   : String,
                         `type` : String)
  case class Predicate  (name : String,
                         args : List[Argument])
  case class FunctionDef(return_type : String,
                         args        : List[Argument],
                         body        : String)
  case class ParsedEncoding(
    ptr_type     : String,
    global_decls : Option[List[Declaration]],
    predicates   : Option[List[Predicate]],
    init_code    : List[String],
    read_fn      : FunctionDef,
    write_fn     : FunctionDef,
    alloc_fn     : FunctionDef,
    free_fn      : FunctionDef
  )

  object EncodingYamlProtocol extends DefaultYamlProtocol {
    implicit val argumentFormat    : YamlFormat[Argument]       = yamlFormat2(Argument)
    implicit val declarationFormat : YamlFormat[Declaration]    = yamlFormat3(Declaration)
    implicit val predicateFormat   : YamlFormat[Predicate]      = yamlFormat2(Predicate)
    implicit val functionDefFormat : YamlFormat[FunctionDef]    = yamlFormat3(FunctionDef)
    implicit val encodingFormat    : YamlFormat[ParsedEncoding] = yamlFormat8(ParsedEncoding)
  }

  def parse(encodingName : String) : ParsedEncoding = {
    val resourcePath = s"tricera/heap/encodings/$encodingName.yml"
    val inputStream = Option(getClass.getClassLoader.getResourceAsStream(resourcePath))
      .getOrElse {
        throw new TranslationException(
          s"Could not find encoding file for '$encodingName'. " +
          s"Expected to find it at 'resources/$resourcePath'")
      }
    val source = scala.io.Source.fromInputStream(inputStream)
    try {
      import EncodingYamlProtocol._
      val yamlAst = source.mkString.parseYaml
      yamlAst.convertTo[ParsedEncoding]
    } catch {
      case e: Throwable =>
        throw new TranslationException(s"Failed to parse encoding file for " +
                                       s"'$encodingName': ${e.getMessage}")
    } finally {
      source.close()
    }
  }
}
