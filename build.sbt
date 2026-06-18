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

// On mistmatch with version stamp, tri-pp will be redownloaded.
// Delete version stamp to use custom tri-pp.
lazy val triPpVersion = "v0.3.0"

def triPpAsset: String = {
  val os   = sys.props.getOrElse("os.name", "").toLowerCase
  val arch = sys.props.getOrElse("os.arch", "").toLowerCase
  val arm  = arch == "aarch64" || arch == "arm64"
  if (os.contains("linux"))
    if (arm) "tri-pp-linux-arm64" else "tri-pp-linux-x64"
  else if (os.contains("mac") || os.contains("darwin"))
    if (arm) "tri-pp-macos-arm64"
    else sys.error(
      "No tri-pp binary for Intel (x86_64) macOS: only Apple Silicon (arm64) " +
      "binaries are published, and those do not run on Intel Macs. Build " +
      "tri-pp from source and point TRI_PP_PATH at it.")
  else if (os.contains("win"))
    sys.error(
      "No native tri-pp for Windows. Run TriCera under WSL (it will use the " +
      "Linux x86_64 binary), or build tri-pp from source and set TRI_PP_PATH.")
  else sys.error(s"Unsupported OS '$os' (arch '$arch') for tri-pp.")
}

def triPpSha256(f: File): String = {
  val md = java.security.MessageDigest.getInstance("SHA-256")
  md.digest(IO.readBytes(f)).map(b => "%02x".format(b & 0xff)).mkString
}

// A bad download (404 body, truncation, tampering) fails the checksum and aborts
def downloadTriPp(asset: String, dest: File, log: Logger): Unit = {
  val base = s"https://github.com/zafer-esen/tri-pp/releases/download/$triPpVersion"
  log.info(s"Downloading tri-pp $triPpVersion ($asset) ...")
  (url(s"$base/$asset") #> dest) !
  val shaTmp = java.io.File.createTempFile("tri-pp-", ".sha256")
  try {
    (url(s"$base/$asset.sha256") #> shaTmp) !
    val expected = IO.read(shaTmp).trim.split("\\s+").headOption.getOrElse("").toLowerCase
    val actual   = triPpSha256(dest)
    if (expected.isEmpty || actual != expected) {
      dest.delete()
      sys.error(s"tri-pp checksum mismatch for $asset from $base:\n" +
                s"  expected: $expected\n  got:      $actual")
    }
    log.info(s"tri-pp $triPpVersion ($asset) verified (sha256 $actual).")
  } finally shaTmp.delete()
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

lazy val ppWithErrorHandling = taskKey[Unit]("Download and verify the pinned tri-pp preprocessor")
ppWithErrorHandling := {
  val log    = streams.value.log
  val binary = baseDirectory.value / "tri-pp"
  val stamp  = baseDirectory.value / ".tri-pp-version"
  if (sys.env.contains("TRI_PP_PATH")) {
    // a developer is supplying their own tri-pp at runtime; do not fetch one
    log.info("TRI_PP_PATH is set; skipping tri-pp download.")
  } else {
    val asset = triPpAsset
    val pin   = s"$triPpVersion $asset"
    if (binary.exists && binary.length > 0) {
      val stamped = if (stamp.exists) IO.read(stamp).trim else ""
      if (stamped == pin)
        log.info(s"tri-pp $pin present; skipping download.")
      else if (stamped.nonEmpty) {
        // a binary we downloaded earlier, but the pin moved on -> upgrade
        log.info(s"tri-pp pin changed ($stamped -> $pin); re-downloading.")
        downloadTriPp(asset, binary, log)
        IO.write(stamp, pin)
      } else
        // an unmanaged binary: a local build (kept as a manual override) or an
        // old checkout from before this stamp existed. We never clobber it;
        // delete ./tri-pp to fetch the pinned release instead.
        log.info("Using existing ./tri-pp without a version stamp (manual " +
                 s"override). Delete ./tri-pp to fetch the pinned $triPpVersion.")
    } else {
      downloadTriPp(asset, binary, log)
      IO.write(stamp, pin)
    }
    if (binary.exists) addExecutePermissions(binary)
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
    // exclude java-cup from transitive dependencies, ccParser includes newer version
      ExclusionRule("net.sf.squirrel-sql.thirdparty-non-maven", "java-cup")),

    Compile / resourceGenerators += Def.task {
      val encodingsDir = (Compile / resourceDirectory).value / "tricera" / "heap" / "encodings"
      val listFile = (Compile / resourceManaged).value / "tricera" / "heap" / "encodings" / "encodings.list"
      if (encodingsDir.isDirectory) {
        val names = encodingsDir.listFiles()
          .filter(_.getName.endsWith(".yml"))
          .map(_.getName.stripSuffix(".yml"))
          .sorted
          .mkString("\n")
        IO.write(listFile, names)
        Seq(listFile)
      } else Seq.empty
    }.taskValue,

    nativeImageInstalled := true,
    // point to GraalVM (recommended via env var)
    //nativeImageGraalHome := file(sys.env("GRAALVM_HOME")).toPath,

    nativeImageOptions ++= Seq(
      "--no-fallback",
      "-H:+ReportExceptionStackTraces",
      "-H:IncludeResources=tricera/headers/.*\\.h",
      "-H:IncludeResources=tricera/heap/encodings/.*\\.yml",
      "-H:IncludeResources=tricera/heap/encodings/encodings\\.list"
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

