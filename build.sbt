
lazy val commonSettings = Seq(
  name := "Horn-Concurrency",
  organization := "uuverifiers",
  version := "1.0",
  scalaVersion := "2.11.12",
  crossScalaVersions := Seq("2.11.12", "2.12.10"),
  homepage := Some(url("https://github.com/uuverifiers/horn-concurrency")),
  licenses := Seq("BSD License 2.0" -> url("https://github.com/uuverifiers/eldarica/blob/master/LICENSE")),
  publishTo := Some(Resolver.file("file",  new File( "/home/wv/public_html/maven/" )) )
)

// Jar files for the parsers

lazy val parserSettings = Seq(
  publishArtifact in packageDoc := false,
  publishArtifact in packageSrc := false,
  exportJars := true,
  crossPaths := true
)

test in assembly := {}

// Project

lazy val root = (project in file(".")).
  settings(commonSettings: _*).

//
settings(
  //scalaSource in Compile := baseDirectory.value / "src",
  //
  //scalaSource in Test := baseDirectory.value / "test/scala",
  //
  scalacOptions in Compile ++=
    List("-feature",
         "-language:implicitConversions,postfixOps,reflectiveCalls"),
  scalacOptions += (scalaVersion map { sv => sv match {
                                        case "2.11.12" => "-optimise"
                                        case "2.12.10" => "-opt:_"
                                      }}).value,
  resolvers += "uuverifiers" at "http://logicrunch.research.it.uu.se/maven/",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.0" % "test",
  libraryDependencies += "uuverifiers" %% "eldarica" % "nightly-SNAPSHOT"
)
  //
