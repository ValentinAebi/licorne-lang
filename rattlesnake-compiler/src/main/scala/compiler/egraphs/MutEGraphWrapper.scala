package compiler.egraphs

import compiler.lang.Formulas.Formula

/**
 * Note: this uses the EGraphs (which are '''immutable''') under the hood, and should thus not be considered an efficient implementation of e-graphs!
 */
final class MutEGraphWrapper(initGraph: EGraph) {
  private var eGraph: EGraph = initGraph

  def getCurrentState: EGraph = eGraph

  def addNode(n: ENode): EClassId = wrappedMethod(_.nodeAdded(n))

  def absorbFormula(f: Formula): EClassId = wrappedMethod(_.withFormulaAbsorbed(f))

  def assertEquality(n1: ENode, n2: ENode): Unit = wrappedMethod(_.withEquality(n1, n2) -> ())

  def assertEquality(f1: Formula, f2: Formula): Unit = wrappedMethod(_.withEquality(f1, f2) -> ())

  def assertEquality(clId1: EClassId, clId2: EClassId): Unit = wrappedMethod(_.withEquality(clId1, clId2) -> ())

  def areEqual(n1: ENode, n2: ENode): Boolean = eGraph.areEqual(n1, n2)

  def areEqual(clId1: EClassId, clId2: EClassId): Boolean = eGraph.areEqual(clId1, clId2)

  def areEqual(f1: Formula, f2: Formula): Boolean = wrappedMethod(_.areEqual(f1, f2))

  private def wrappedMethod[T](mth: EGraph => (EGraph, T)): T = {
    val (newGraph, t) = mth(eGraph)
    eGraph = newGraph
    t
  }

}

object MutEGraphWrapper {

  def newEmpty: MutEGraphWrapper = {
    val gen = new EClassId.Generator
    MutEGraphWrapper(EGraph.empty(using gen))
  }

}
