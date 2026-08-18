package compiler.stdlib

import compiler.identifiers.TypeIdentifier

object Names {

  private val licornePkgPrefix = List("licorne")
  private val licorneClosuresPkgPrefix = licornePkgPrefix :+ "closures"

  val heapVar: TypeIdentifier = TypeIdentifier(licorneClosuresPkgPrefix, "HeapVar")
  val intHeapVar: TypeIdentifier = TypeIdentifier(licorneClosuresPkgPrefix, "IntHeapVar")

}
