ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.4"

ThisBuild / libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.4.0"
ThisBuild / libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % Test

lazy val root = (project in file("."))
  .settings(
    name := "software-testing"
  )
