package compiler.backend

import java.io.File

object JarFinder {

  def findNameOfJarInDir(dir: File, jarNamePrefix: String): Option[String] = {
    dir.list().find(f => f.startsWith(jarNamePrefix) && f.endsWith(".jar"))
  }
  
}
