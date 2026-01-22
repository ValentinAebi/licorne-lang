name := "Rattlesnake"

version := "0.2.0-SNAPSHOT"

scalaVersion := "3.7.3"
javacOptions ++= Seq("-source", "21", "-target", "21")

libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test"

assembly / assemblyMergeStrategy := {
  case PathList("META-INF", _*) => MergeStrategy.discard
  case _                        => MergeStrategy.first
}
