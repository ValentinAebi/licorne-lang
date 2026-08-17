package compiler.backend

import scala.collection.mutable

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier

// TODO this could be optimized by not using the Graph methods, and use the memo for intermediate steps
final class SimplifiedSubtypingContext(subtypingGraph: Graph[TypeIdentifier]) {
  private val isSubtypeMemo = mutable.Map.empty[(TypeIdentifier, TypeIdentifier), Boolean]

  def isSubtype(subT: TypeIdentifier, superT: TypeIdentifier): Boolean = isSubtypeMemo.getOrElseUpdate((subT, superT), {
    subtypingGraph.shortestPathUnweighted(subT, superT).isDefined
  })
  
}
