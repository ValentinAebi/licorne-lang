name := "licorne-lang"

version := "0.3.0-SNAPSHOT"

scalaVersion := "3.8.0"
javacOptions ++= Seq("-source", "25", "-target", "25")

libraryDependencies += "com.github.sbt" % "junit-interface" % "0.13.3" % Test

libraryDependencies += "io.ksmt" % "ksmt-core" % "0.6.4"
libraryDependencies += "io.ksmt" % "ksmt-z3" % "0.6.4"

assembly / assemblyMergeStrategy := {
  case PathList("META-INF", _*) => MergeStrategy.discard
  case _                        => MergeStrategy.first
}
