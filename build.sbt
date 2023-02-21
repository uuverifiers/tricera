import scala.sys.process._ // needed for url to fetch tri-pp
import java.nio.file.{Paths, Files}
import java.nio.file.attribute.PosixFilePermission._

lazy val commonSettings = Seq(
    name                 := "TriCera",
    organization         := "uuverifiers",
    version              := "0.2",
    homepage             := Some(url("https://github.com/uuverifiers/tricera")),
    licenses             := Seq("BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause")),
    description          := "TriCera is a model checker for C programs.",
    scalaVersion         := "2.11.12",
    crossScalaVersions   := Seq("2.11.12", "2.12.8"),
    publishTo            := Some(Resolver.file("file",  new File( "/home/wv/public_html/maven/" )) ),
    useCoursier          := false
)

// Jar files for the parsers

lazy val parserSettings = Seq(
    publishArtifact in packageDoc := false,
    publishArtifact in packageSrc := false,
    exportJars := true,
    crossPaths := true
)

// Parser generation

lazy val ccParser = (project in file("cc-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "TriCera-CC-parser",
    packageBin in Compile := baseDirectory.value / "cc-parser.jar"
  ).disablePlugins(AssemblyPlugin)

lazy val acslParser = (project in file("acsl-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "TriCera-ACSL-parser",
    packageBin in Compile := baseDirectory.value / "acsl-parser.jar"
  ).disablePlugins(AssemblyPlugin)

lazy val pp = taskKey[Unit]("")
pp := {
  val f = url("https://github.com/zafer-esen/tri-pp/releases/download/v0.1.1/tri-pp")
  f #> file("tri-pp") !
}
def addExecutePermissions(file : File) {
  val rf = fileToRichFile(file)
  val permissions = Seq(OTHERS_EXECUTE, OWNER_EXECUTE, GROUP_EXECUTE).toSet
  if(!permissions.subsetOf(rf.permissions)) {
    permissions.foreach(rf.addPermission(_))
  }
}
lazy val ppWithErrorHandling = taskKey[Unit]("Download the preprocessor")
ppWithErrorHandling := {
  if ({val f = baseDirectory.value / "tri-pp"
        Files.exists(Paths.get(f.toString)) &&
          fileToRichFile(f).attributes.size > 0}) {
    println("tri-pp found, skipping download.")
    addExecutePermissions(baseDirectory.value / "tri-pp")
  }
  else {
    pp.result.value match{
      case Inc(inc : Incomplete) =>
        println("failure! Please double check the link in build.sbt" +
                  " and make sure it exists.")
      case _ =>
        println("tri-pp downloaded.")
        addExecutePermissions(baseDirectory.value / "tri-pp")
    }
  }
}
  (compile in Compile) := ((compile in Compile) dependsOn ppWithErrorHandling).value

// Actual project
lazy val root = (project in file(".")).
  aggregate(ccParser).
  dependsOn(ccParser).
  aggregate(acslParser).
  dependsOn(acslParser).
  settings(commonSettings: _*).

//
settings(
  scalaSource in Compile := baseDirectory.value / "src",
  //
  scalaSource in Test := baseDirectory.value / "unit-tests",
  //
  mainClass in Compile := Some("tricera.Main"),
  //
  scalacOptions in Compile ++=
    List("-feature",
         "-language:implicitConversions,postfixOps,reflectiveCalls"),
  scalacOptions += (scalaVersion map { sv => sv match {
                                        case "2.11.12" => "-optimise"
                                        case "2.12.8" => "-opt:_"
                                      }}).value,
  resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/").withAllowInsecureProtocol(true),
  libraryDependencies += "uuverifiers" %% "eldarica" % "nightly-SNAPSHOT",
  libraryDependencies += "uuverifiers" %% "horn-concurrency" % "1.1",
  libraryDependencies += "net.jcazevedo" %% "moultingyaml" % "0.4.2",
  libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.12",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.12" % "test",
  excludeDependencies ++= Seq(
    // exclude java-cup from transitive dependencies, ccParser includes newer version
    ExclusionRule("net.sf.squirrel-sql.thirdparty-non-maven", "java-cup"))
)

// project can also be built by providing dependencies under the lib directory
// and uncommenting below code to discard clashing transitive dependencies
//assemblyMergeStrategy in assembly := {
//  case PathList("META-INF", xs @ _*) => MergeStrategy.discard
//  case x => MergeStrategy.last
//}
