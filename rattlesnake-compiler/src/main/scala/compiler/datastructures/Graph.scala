package compiler.datastructures

import scala.annotation.tailrec
import scala.collection.mutable
import scala.reflect.ClassTag
import scala.util.boundary

final class Graph[N] private(verticesToAdjSets: Map[N, Set[N]]) {

  def adjSetOf(n: N): Set[N] = verticesToAdjSets.getOrElse(n, Set.empty)

  val vertices: Set[N] = verticesToAdjSets.keySet

  def findShortestCycle(): Option[Seq[N]] = {
    if (vertices.isEmpty) {
      return None
    }

    val orderedVertices = vertices.toIndexedSeq
    val verticesOrdering = orderedVertices.zipWithIndex.toMap
    val distancesTable = Array.fill(vertices.size, vertices.size)(-1 -> Option.empty[N])

    def tableGet(from: N, to: N): (Int, Option[N]) = {
      val rowIdx = verticesOrdering.apply(from)
      val colIdx = verticesOrdering.apply(to)
      distancesTable(rowIdx)(colIdx)
    }

    def tableSet(from: N, to: N, distance: Int, pred: Option[N]): Unit = {
      val rowIdx = verticesOrdering.apply(from)
      val colIdx = verticesOrdering.apply(to)
      distancesTable(rowIdx)(colIdx) = (distance, pred)
    }

    for (root <- vertices) {
      tableSet(root, root, 0, None)
      val worklist = mutable.Queue.empty[N]
      val reached = mutable.Set.empty[N]

      worklist.enqueue(root)
      while (worklist.nonEmpty) {
        val curr = worklist.dequeue()
        val (dist, _) = tableGet(root, curr)
        for (desc <- adjSetOf(curr)) {
          if (reached.add(desc)) {
            tableSet(root, desc, dist + 1, Some(curr))
            worklist.enqueue(desc)
          }
        }
      }
    }

    var (minCycleElem, minCycleLen) = (vertices.head, Int.MaxValue)
    for (u <- vertices) {
      val (minUCycleLen, _) = tableGet(u, u)
      if (minUCycleLen > 0 && minUCycleLen < minCycleLen) {
        minCycleElem = u
        minCycleLen = minUCycleLen
      }
    }

    if (minCycleLen == Int.MaxValue){
      None
    } else {
      var cycle = List.empty[N]
      var curr = tableGet(minCycleElem, minCycleElem)._2.get
      cycle = curr :: cycle
      while (curr != minCycleElem) {
        curr = tableGet(minCycleElem, curr)._2.get
        cycle = curr :: cycle
      }
      Some(cycle)
    }
  }

  def shortestPath(from: N, to: N): Option[Seq[N]] = {
    val predecessor = mutable.Map.empty[N, N]

    @tailrec
    def buildPathBack(n: N, tail: List[N]): List[N] = {
      if n == from then n :: tail
      else buildPathBack(predecessor.apply(n), n :: tail)
    }

    boundary {
      val worklist = mutable.Queue.empty[N]
      worklist.enqueue(from)
      while (worklist.nonEmpty) {
        val curr = worklist.dequeue()
        for (desc <- adjSetOf(curr)) {
          if (desc == to) {
            boundary.break(Some(buildPathBack(curr, List(to))))
          }
          if (!predecessor.contains(desc)) {
            predecessor(desc) = curr
            worklist.enqueue(desc)
          }
        }
      }
      None
    }
  }

}

object Graph {

  final class Builder[N] {
    private val adjSets = mutable.Map.empty[N, mutable.Set[N]]

    def addVertex(n: N): this.type = {
      if (!adjSets.contains(n)) {
        adjSets(n) = mutable.Set.empty
      }
      this
    }

    def addEdge(from: N, to: N): this.type = {
      addVertex(from)
      addVertex(to)
      adjSets.apply(from).add(to)
      this
    }

    def build(): Graph[N] =
      Graph(adjSets.toMap.map((n, as) => n -> as.toSet))

  }

}
