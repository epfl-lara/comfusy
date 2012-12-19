name := "comfusy-synthesis"

libraryDependencies <++= (scalaBinaryVersion)(sv =>
  Seq(
    "org.scala-lang" % "scala-compiler" % sv
    // "org.scalatest" % "scalatest_2.10.0-M7" % "1.9-2.10.0-M7-B1" % "test"
    // "org.scalatest" %% "scalatest" % "1.9-2.10.0-M5-B2" % "test"
    // scalatest_2.10.0-M7/1.9-2.10.0-M7-B1
  )
)

// libraryDependencies ++= Seq(
//   "org.scalatest" %% "scalatest" % "1.6.1"
// )
