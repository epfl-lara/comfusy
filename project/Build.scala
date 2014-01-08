import sbt._
import Keys._

object Comfusy extends Build {
  val commonSettings = Seq(
    name                 := "comfusy",
    organization         := "org.improving",
    scalaVersion         := "2.10.3",
    // scalaBinaryVersion   := "2.10.3",
    version              := "1.0.0",
    scalacOptions       ++= Seq("-deprecation", "-unchecked"),
    libraryDependencies  += "org.scala-lang" % "scala-compiler" % scalaVersion.value,
    libraryDependencies  += "org.scalatest" %% "scalatest" % "2.0" % "test"
  )

  lazy val comfusy  = Project(id = "comfusy", base = file(".")).settings(commonSettings: _*)
}
