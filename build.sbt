
lazy val commonSettings = Seq(
    name := "TriCera",
    organization := "uuverifiers",
    version := "2.0",
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

// Actual project

lazy val root = (project in file(".")).
    aggregate(ccParser).
    dependsOn(ccParser).
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

    resolvers += "uuverifiers" at "http://logicrunch.research.it.uu.se/maven/",
    libraryDependencies += "uuverifiers" %% "eldarica" % "2.1.0"
)
//
