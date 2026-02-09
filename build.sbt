import scala.sys.process._
import java.nio.file.{Files, Paths}
import java.nio.file.attribute.PosixFilePermissions
import scala.language.postfixOps
import scala.util.Try
import sbt._
import Keys._

lazy val commonSettings = Seq(
    name                 := "TriCera",
    organization         := "uuverifiers",
    version              := "0.4-DEV",
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
  val f = url("https://github.com/zafer-esen/tri-pp/releases/download/v0.1.3/tri-pp")
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

lazy val princess = ProjectRef(file("princess"), "root")
lazy val eldarica = ProjectRef(file("eldarica"), "root")
lazy val hornConcurrency = ProjectRef(file("horn-concurrency"), "root")

// Actual project

lazy val root = (project in file("."))
  .settings(commonSettings)
  .settings(
    mainClass in Compile := Some("tricera.Main"),
    scalacOptions in Compile ++=
    List("-feature", "-language:implicitConversions,postfixOps,reflectiveCalls",
         "-encoding", "UTF-8"),
    scalacOptions += "-opt:_",
    //resolvers += "uuverifiers" at "https://eldarica.org/maven/",
    libraryDependencies ++= Seq(
      "net.jcazevedo" %% "moultingyaml" % "0.4.2",
      "org.scalactic" %% "scalactic" % "3.2.19",
      "org.scalatest" %% "scalatest" % "3.2.19" % Test
      ),
    excludeDependencies ++= Seq(
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
  .dependsOn(ccParser, acslParser, eldarica, hornConcurrency)
  .aggregate(ccParser, acslParser)
  .enablePlugins(NativeImagePlugin)

// Remove java-cup-11a jars from unmanagedJars in subprojects
ccParser / Compile / unmanagedJars :=
(ccParser / Compile / unmanagedJars).value.filterNot(
  _.data.getName.contains("java-cup-11a"))

lazy val settingsAlreadyOverridden = settingKey[Boolean](
  "Has overrideSettings command already run?")
settingsAlreadyOverridden := false

commands += Command.command("overrideSettings") { state =>
  val extracted = Project.extract(state)
  if (extracted.get(settingsAlreadyOverridden)) state
  else {
    Project.extract(state).appendWithSession(
      Seq(
        settingsAlreadyOverridden := true,
        eldarica / organization        := "uuverifiers-dev",
        eldarica / version             := "0.0.0-dev",
        hornConcurrency / organization := "uuverifiers-dev",
        hornConcurrency / version      := "0.0.0-dev",
        princess / organization        := "uuverifiers-dev",
        princess / version             := "0.0.0-dev",

        eldarica / libraryDependencies := (eldarica / libraryDependencies).value.filterNot(_.organization.startsWith("uuverifiers")),
        hornConcurrency / libraryDependencies := (hornConcurrency / libraryDependencies).value.filterNot(_.organization.startsWith("uuverifiers")),
        ),
      state
      )
  }
}

onLoad in Global := {
  ((s: State) => "overrideSettings" :: s) compose (onLoad in Global).value
}

assembly / assemblyMergeStrategy := {
  case PathList("java_cup", "runtime", _ @ _*) => MergeStrategy.first
  case PathList("META-INF", _ @ _*) => MergeStrategy.discard
  case x => MergeStrategy.first
}

