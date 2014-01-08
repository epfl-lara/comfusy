name := "comfusy"

organization := "org.improving"

scalaVersion := "2.10.3"

version := "1.0.0"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-compiler" % scalaVersion.value,
  "org.scalatest" %% "scalatest" % "2.0" % "test"
)
