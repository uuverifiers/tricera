import scala.sys.process._
import java.nio.file.{Files, Paths}
import java.nio.file.attribute.PosixFilePermissions
import scala.language.postfixOps
import scala.util.Try

lazy val commonSettings = Seq(
    name                 := "TriCera",
    organization         := "uuverifiers",
    version              := "0.4",
    homepage             := Some(url("https://github.com/uuverifiers/tricera")),
    licenses             := Seq("BSD-3-Clause" -> url("https://opensource.org/licenses/BSD-3-Clause")),
    description          := "TriCera is a model checker for C programs.",
    scalaVersion         := "2.13.17", // released 2025-10-06
    crossScalaVersions   := Seq("2.13.17"),
    publishTo            := Some(Resolver.file("file",  new File( "/home/compilation/public_html/maven/" )) ),
    useCoursier          := false
)

lazy val parserSettings = Seq(
    publishArtifact in packageDoc := false,
    publishArtifact in packageSrc := false,
    exportJars := true,
    crossPaths := true
)

lazy val ccParser = (project in file("cc-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "TriCera-CC-parser",
    packageBin in Compile := baseDirectory.value / "cc-parser.jar",
    unmanagedJars in Compile += baseDirectory.value / "cc-parser.jar"
  ).disablePlugins(AssemblyPlugin)

lazy val acslParser = (project in file("acsl-parser")).
  settings(commonSettings: _*).
  settings(parserSettings: _*).
  settings(
    name := "TriCera-ACSL-parser",
    packageBin in Compile := baseDirectory.value / "acsl-parser.jar",
    unmanagedJars in Compile += baseDirectory.value / "acsl-parser.jar"
  ).disablePlugins(AssemblyPlugin)

lazy val pp = taskKey[Unit]("")
pp := {
  val f = url("https://github.com/zafer-esen/tri-pp/releases/download/v0.2.0/tri-pp-ubuntu-22.04")
  f #> file("tri-pp") !
}

def addExecutePermissions(file: File): Unit = {
  val path = Paths.get(file.getAbsolutePath)
  if (Files.exists(path)) {
    val fileSystem = path.getFileSystem
    if (fileSystem.supportedFileAttributeViews().contains("posix")) {
      Try {
        val permissions = PosixFilePermissions.fromString("rwxr-xr-x")
        Files.setPosixFilePermissions(path, permissions)
        println(s"Set execute permissions on ${file.getAbsolutePath}")
      }.getOrElse {
        println(s"Could not set execute permissions on ${file.getAbsolutePath}")
      }
    } else {
      println(s"Skipping permission changes: " +
        s"${file.getAbsolutePath} is on a non-POSIX filesystem (${fileSystem.provider()}).")
    }
  } else {
    println(s"File not found: ${file.getAbsolutePath}")
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
  mainClass in Compile := Some("tricera.Main"),
  //
  scalacOptions in Compile ++=
    List("-feature",
         "-language:implicitConversions,postfixOps,reflectiveCalls"),
  scalacOptions += "-opt:_",
  resolvers += "uuverifiers" at "https://eldarica.org/maven/",
  libraryDependencies += "uuverifiers" %% "eldarica" % "2.2.1",
  libraryDependencies += "uuverifiers" %% "horn-concurrency" % "2.2.1",
  libraryDependencies += "net.jcazevedo" %% "moultingyaml" % "0.4.2",
  libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.19",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % "test",
  excludeDependencies ++= Seq(
    // exclude java-cup from transitive dependencies, ccParser includes newer version
    ExclusionRule("net.sf.squirrel-sql.thirdparty-non-maven", "java-cup")),

    nativeImageInstalled := false,
    nativeImageVersion := "21.1.0",
    nativeImageJvm := "graalvm-java11",
    // point to GraalVM (recommended via env var)
    //nativeImageGraalHome := file(sys.env("GRAALVM_HOME")).toPath,

    nativeImageOptions ++= Seq(
      "--no-fallback",
      "-H:+ReportExceptionStackTraces",
      "--allow-incomplete-classpath"
    ),

    nativeImageAgentMerge := true
  )
 .enablePlugins(NativeImagePlugin)

// project can also be built by providing dependencies under the lib directory
// and uncommenting below code to discard clashing transitive dependencies
//assemblyMergeStrategy in assembly := {
//  case PathList("META-INF", xs @ _*) => MergeStrategy.discard
//  case x => MergeStrategy.last
//}
