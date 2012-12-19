import sbt._
import Keys._

object Comfusy extends Build {
  val commonSettings = Seq(
    scalaVersion := "2.10.0-RC5",
    scalaBinaryVersion := "2.10.0-RC5",
    organization := "org.improving",
    version := "1.0.0",
    scalacOptions ++= Seq("-deprecation", "-unchecked")
  )

  lazy val comfusy = Project(id = "comfusy", base = file(".")).settings(commonSettings: _*) aggregate(synthesis)
  lazy val synthesis  = Project(id = "synthesis", base = file("synthesis")).settings(commonSettings: _*)
  // lazy val decision  = Project(id = "decision", base = file("decision")).settings(commonSettings: _*) dependsOn synthesis
}
