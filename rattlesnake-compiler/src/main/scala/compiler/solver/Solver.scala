package compiler.solver

import compiler.datastructures.Graph
import lang.Formulas.{Formula, LessOrEq, LessThan}
import lang.Types.{IntRangeType, Type}
import lang.Types.IntRangeType.Bound
import lang.Types.PrimitiveType.NothingType

import scala.util.boundary

trait Solver {

  def assert(formula: Formula): Unit

  def canProve(formula: Formula): Boolean

  def isSatisfiable(formula: Formula): Boolean

  def simplifyRange(range: IntRangeType): Type = {
    val IntRangeType(low, up) = range
    val afterFirstStep = IntRangeType(simplifyBound(low), simplifyBound(up))
    // TODO also try to map to a singleton type if [a,b] with a == b
    if canProveNothing(afterFirstStep) then NothingType else afterFirstStep
  }

  def canProveNothing(range: IntRangeType): Boolean = boundary {
    range.lowerBound.collectFormulas { l =>
      range.upperBound.collectFormulas { u =>
        if (canProve(LessThan(u, l))) {
          boundary.break(true)
        }
      }
    }
    false
  }

  def simplifyBound(bound: IntRangeType.Bound): IntRangeType.Bound = bound match {
    case Bound.Max(bounds) =>
      val leqGraph = mkLessOrEqGraph(bounds)
      val sccLeqGraph = leqGraph.sccGraph()
      val dominators = sccLeqGraph.verticesOfOutDegree(0).map(_.head)
      Bound.Max(dominators)
    case Bound.Min(bounds) =>
      val leqGraph = mkLessOrEqGraph(bounds)
      val sccLeqGraph = leqGraph.sccGraph()
      val dominated = sccLeqGraph.verticesOfInDegree(0).map(_.head)
      Bound.Min(dominated)
    case bound => bound
  }

  private def mkLessOrEqGraph(bounds: Set[Formula]): Graph[Formula] = {
    val graphB = Graph.Builder[Formula]()
    for (b <- bounds) {
      graphB.addVertex(b)
    }
    for (b1 <- bounds; b2 <- bounds) {
      if (canProve(LessOrEq(b1, b2))) {
        graphB.addEdge(b1, b2)
      }
    }
    val graph = graphB.build()
    graph
  }

}
