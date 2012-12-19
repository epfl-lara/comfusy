name := "comfusy-decision"

libraryDependencies += "org.improving" %% "comfusy-synthesis" % "1.0.0-SNAPSHOT"

autoCompilerPlugins := true

scalacOptions ++= Seq("-Xpluginsdir", "/s/comfusy/synthesis/target/scala-2.9.2", "-Xplugin-require:synthesis")
