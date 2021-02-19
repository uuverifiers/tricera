
lazy val commonSettings = Seq(
    name := "TriCera",
    organization := "uuverifiers",
    version := "0.2",
    scalaVersion := "2.11.12",
    crossScalaVersions := Seq("2.11.12", "2.12.8"),
    publishTo := Some(Resolver.file("file",  new File( "/home/wv/public_html/maven/" )) )
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
    val libDir = preprocessorDir / "build"
    val libFile = libDir / "libtricera-preprocessor.so"
    val cacheDir = libDir / ".cache"

    val cache = FileFunction.cached(cacheDir,
                                    inStyle = FilesInfo.lastModified,
                                    outStyle = FilesInfo.exists){ _ =>
      scala.sys.process.Process(
        "cmake -DCT_LLVM_INSTALL_DIR=/usr/lib/llvm-11 " +  preprocessorDir).!
      scala.sys.process.Process("make -j 3").!
        Set()
    }

    cache(sources.get.toSet + libFile).toSeq
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
  libraryDependencies += "uuverifiers" %% "eldarica" % "2.0.5-heap",
  libraryDependencies += "uuverifiers" %% "horn-concurrency" % "1.0",
  libraryDependencies += "net.java.dev.jna" % "jna" % "4.2.2",
  libraryDependencies += "net.jcazevedo" %% "moultingyaml" % "0.4.2"
)
  //
