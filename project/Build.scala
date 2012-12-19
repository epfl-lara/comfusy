import sbt._
import Keys._

object Comfusy extends Build {
  val commonSettings = Seq(
    name := "comfusy",
    organization := "org.improving",
    scalaVersion := "2.10.0-RC5",
    scalaBinaryVersion := "2.10.0-RC5",
    version := "1.0.0",
    scalacOptions ++= Seq("-deprecation", "-unchecked"),
    libraryDependencies <+= (scalaBinaryVersion)("org.scala-lang" % "scala-compiler" % _)
  )

  lazy val comfusy  = Project(id = "comfusy", base = file(".")).settings(commonSettings: _*)
}
