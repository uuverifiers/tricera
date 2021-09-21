
lazy val commonSettings = Seq(
    name := "TriCera",
    organization := "uuverifiers",
    version := "0.2",
    scalaVersion := "2.11.12",
    crossScalaVersions := Seq("2.11.12", "2.12.8"),
    publishTo := Some(Resolver.file("file",  new File( "/home/wv/public_html/maven/" )) ),
    useCoursier := false
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

// horn-concurrency dependency
//lazy val hornConcurrency = RootProject(uri("git://github.com/zafer-esen/horn-concurrency-test.git"))

// Preprocessor generation
lazy val preprocessorGen = Seq(
  sourceGenerators in Compile += Def.task {
    val preprocessorDir = baseDirectory.value / "preprocessor"
    def sources : PathFinder  =
      (preprocessorDir ** "*") ** ("*.hpp" || "*.cpp")
    val buildDir = preprocessorDir / "build"
    val llvmBuildDir = preprocessorDir / "llvm" / "build"
    val execFile = baseDirectory.value / "tri-pp"
    val cacheDir = buildDir / ".cache"

    def buildPreprocessor = {
      scala.sys.process.Process(
        "mkdir -p " +  llvmBuildDir).!
        scala.sys.process.Process(
          "cmake " +  llvmBuildDir + "/.. -B" + llvmBuildDir).!

      scala.sys.process.Process("make -C " + llvmBuildDir + " -j 3").!

      scala.sys.process.Process(
        "cmake " +  buildDir + "/.. -B" + buildDir).!

      scala.sys.process.Process("make install -C " + buildDir + " -j 3").!
    }

    import java.nio.file.{ Files, Paths }
    if (!Files.exists(Paths.get(execFile.toString)))
      buildPreprocessor

    val cache = FileFunction.cached(cacheDir,
                                    inStyle = FilesInfo.lastModified){ _ =>
      buildPreprocessor
      Set()
    }
    cache(sources.get.toSet).toSeq
  }.taskValue
 )

// Actual project

lazy val root = (project in file(".")).
  aggregate(ccParser).
  dependsOn(ccParser).
  // dependsOn(hornConcurrency).
  settings(preprocessorGen: _*).
  settings(commonSettings: _*).

//
settings(
  scalaSource in Compile := baseDirectory.value / "src",
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
  libraryDependencies += "uuverifiers" %% "eldarica" % "2.0.6",
  libraryDependencies += "uuverifiers" %% "horn-concurrency" % "nightly-SNAPSHOT",
  libraryDependencies += "net.jcazevedo" %% "moultingyaml" % "0.4.2"
)

// added to discard cup 0.11a dependency from Eldarica (TriCera uses cup 0.11b)
assemblyMergeStrategy in assembly := {
  case PathList("META-INF", xs @ _*) => MergeStrategy.discard
  case x => MergeStrategy.first
}
  //
