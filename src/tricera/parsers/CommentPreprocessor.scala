package tricera.parsers
import java.io.{BufferedReader, BufferedWriter, StringReader, StringWriter}

// preprocesses ACSL style comments to make life easier for the parser
object CommentPreprocessor {
  val annotationMarker = "■■" // ascii 254 times 2
  def apply(reader : BufferedReader, readerBufferSize : Int = 1000) :
  BufferedReader = {
    val stringWriter = new StringWriter(readerBufferSize)
    val writer = new BufferedWriter(stringWriter)

    var isInComment = false

    var line: String = reader.readLine
    var newLine = new scala.collection.mutable.StringBuilder(line.length)
    var curInd = 0

    while (line != null) {
      if (!isInComment) {
        val curSlashInd = line.indexOf("/", curInd)
        curSlashInd match {
          case -1 => // no more slashes
            newLine ++= line.substring(curInd)
            curInd = line.length // will move on to next line
          case i if i < line.length - 2 => // need at least 2 more chars
            line.substring(i + 1, i + 3) match {
              case "*@" =>
                newLine ++= line.substring(curInd, i) ++ annotationMarker
                isInComment = true
                curInd = i + 3
              case "/@" =>
                newLine ++= line.substring(curInd, i) ++ annotationMarker ++
                  line.substring(i + 3) ++ annotationMarker
                curInd = line.length // will move on to next line
              case _ => // found slash but not a comment in our desired format
                newLine ++= line.substring(curInd, i + 1)
                curInd = i + 1
            }
          case _ =>
            newLine ++= line.substring(curInd)
            curInd = line.length
        }
      } else { // is in commment
        val curStarInd = line.indexOf("*", curInd)
        curStarInd match {
          case -1 =>
            newLine ++= line.substring(curInd)
            curInd = line.length // will move on to next line
          case i if i < line.length - 1 && line.charAt(i + 1) == '/' &&
            i > 0 && line.charAt(i - 1) == '@' =>
            newLine ++= line.substring(curInd, i - 1) + annotationMarker
            curInd = i + 2
            isInComment = false
          case i if i < line.length - 1 && line.charAt(i + 1) == '/' =>
            newLine ++= line.substring(curInd, i) ++ annotationMarker
            curInd = i + 2
            isInComment = false
          case i =>
            newLine ++= line.substring(curInd, i + 1)
            curInd = i + 1
        }
      }
      if (curInd >= line.length) {
        line = reader.readLine
        writer.write(newLine.toString ++ "\n") //(if(isInComment) "" else "\n")) // remove new lines as well?
        newLine.clear
        curInd = 0
      }
    }
    stringWriter.close()
    writer.close()

//    println("comment-preprocessed input:\n\n" + stringWriter.getBuffer.toString)

    new BufferedReader(new StringReader(stringWriter.getBuffer.toString))
    // todo: benchmark this with files, >1 MB, benchmark this whole class
  }
}
