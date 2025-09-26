lazy val commonSettings = Seq(
  name := "Horn-Concurrency",
  organization := "uuverifiers",
  version := "2.2",
  scalaVersion := "2.13.15",
  crossScalaVersions := Seq("2.13.15"),
  description := "Encoding of concurrent or replicated programs using Horn clauses",
  homepage := Some(url("https://github.com/uuverifiers/horn-concurrency")),
  licenses := Seq("BSD License 2.0" -> url("https://github.com/uuverifiers/eldarica/blob/master/LICENSE")),
  scmInfo  := Some(ScmInfo(
    url("https://github.com/uuverifiers/horn-concurrency"),
        "scm:git@github.com/uuverifiers/horn-concurrency.git")),
  developers := List(
    Developer(
      id    = "pruemmer",
      name  = "Philipp Ruemmer",
      email = "ph_r@gmx.net",
      url   = url("https://philipp.ruemmer.org")
    ),
    Developer(
      id    = "zafer.esen",
      name  = "Zafer Esen",
      email = "zafer.esen@gmail.com",
      url   = url("https://zafer-esen.github.io/")
    )
  ),
  publishTo := Some(Resolver.file("file",  new File( "/home/compilation/public_html/maven/" )))
)

assembly / test := {}

// Project

lazy val root = (project in file(".")).
  settings(commonSettings: _*).

settings(
  Compile / scalacOptions ++=
    List("-feature",
         "-language:implicitConversions,postfixOps,reflectiveCalls"),
  scalacOptions += (scalaVersion map { sv => sv match {
                                        case "2.13.15" => "-opt:_"
                                      }}).value,
  resolvers += "uuverifiers" at "https://eldarica.org/maven/",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.0" % "test",
  libraryDependencies += "uuverifiers" %% "eldarica" % "2.2" exclude(
    "net.sf.squirrel-sql.thirdparty-non-maven","java-cup")
)
