package compiler.egraphs

import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.lang.Formulas.Formula
import compiler.util.SeqSet

/**
 * Note: this uses the EGraphs (which are '''immutable''') under the hood, and should thus not be considered an efficient implementation of e-graphs!
 */
final class MutEGraphWrapper(initGraph: EGraph) {
  private var eGraph: EGraph = initGraph

  def getCurrentState: EGraph = eGraph

  def ownerClassOf(n: ENode): EClass = eGraph.ownerClassOf(n)

  def addNode(n: ENode): EClassId = wrappedMethod(_.nodeAdded(n))

  def absorbFormula(f: Formula): EClassId = wrappedMethod(_.withFormulaAbsorbed(f))

  def assertEquality(n1: ENode, n2: ENode): Unit = wrappedMethod(_.withEquality(n1, n2) -> ())

  def assertEquality(f1: Formula, f2: Formula): Unit = wrappedMethod(_.withEquality(f1, f2) -> ())

  def assertEquality(clId1: EClassId, clId2: EClassId): Unit = wrappedMethod(_.withEquality(clId1, clId2) -> ())

  def equalityQuery(n1: ENode, n2: ENode): Boolean = eGraph.equalityQuery(n1, n2)

  def equalityQuery(clId1: EClassId, clId2: EClassId): Boolean = eGraph.equalityQuery(clId1, clId2)

  def equalityQueryNoSaturation(f1: Formula, f2: Formula): Boolean = wrappedMethod(_.equalityQueryNoSaturation(f1, f2))

  def equalityQueryAfterSaturation(f1: Formula, f2: Formula, rules: List[EqualitySaturationRewriteRule], maxStepsCnt: Long): Boolean =
    wrappedMethod(_.equalityQueryAfterSaturation(f1, f2, rules, maxStepsCnt))

  def runEqualitySaturation(rules: List[EqualitySaturationRewriteRule], maxStepsCnt: Int): Unit =
    wrappedMethod(_.afterEqualitySaturation(rules, maxStepsCnt) -> ())

  private def wrappedMethod[T](mth: EGraph => (EGraph, T)): T = {
    val (newGraph, t) = mth(eGraph)
    eGraph = newGraph
    t
  }

  override def toString: String =
    s"Wrapper {\n" + eGraph.toString.indent(3) + "}"

}

object MutEGraphWrapper {

  def newEmpty: MutEGraphWrapper = {
    val gen = new EClassId.Generator
    MutEGraphWrapper(EGraph.empty(using gen))
  }

}
