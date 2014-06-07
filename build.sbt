name := "comfusy"

organization := "org.improving"

scalaVersion := "2.11.1"

version := "1.0.0"

scalacOptions ++= Seq("-deprecation", "-unchecked")

libraryDependencies ++= Seq(
  "org.scala-lang" % "scala-compiler" % scalaVersion.value,
  "org.scalatest" %% "scalatest" % "2.2.0" % "test"
)

// lame
conflictWarning ~= { _.copy(failOnConflict = false) }
