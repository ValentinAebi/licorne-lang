package datastructures

import scala.annotation.tailrec
import scala.collection.mutable
import scala.reflect.{ClassTag, classTag}
import scala.util.boundary

final class Graph[N] private(verticesToAdjSets: Map[N, Set[N]]) {

  def adjSetOf(n: N): Set[N] = verticesToAdjSets.getOrElse(n, Set.empty)

  def inSetOf(n: N): Set[N] = inSetsMemo.getOrElse(n, Set.empty)

  val vertices: Set[N] = verticesToAdjSets.keySet

  def edges: Set[(N, N)] = for {
    from <- vertices
    to <- adjSetOf(from)
  } yield from -> to

  def verticesOfInDegree(inDeg: Int): Set[N] = {
    vertices.filter(inSetOf(_).size == inDeg)
  }

  def verticesOfOutDegree(outDeg: Int): Set[N] = {
    vertices.filter(adjSetOf(_).size == outDeg)
  }

  private lazy val inSetsMemo = computeInSets()

  private def computeInSets(): Map[N, Set[N]] = {
    val inSetMap = mutable.Map.empty[N, Set[N]]
    for ((from, to) <- edges) {
      inSetMap.updateWith(to) {
        case None => Some(Set(from))
        case Some(preSet) => Some(preSet + from)
      }
    }
    inSetMap.toMap
  }

  def findShortestCycle(): Option[Seq[N]] = shortestCycleMemo

  private lazy val shortestCycleMemo = computeShortestCycle()

  private def computeShortestCycle(): Option[Seq[N]] = {
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

    if (minCycleLen == Int.MaxValue) {
      None
    } else {
      var cycle = List.empty[N]
      var curr = tableGet(minCycleElem, minCycleElem)._2.get
      cycle = curr :: cycle
      while (curr != minCycleElem) {
        curr = tableGet(minCycleElem, curr)._2.get
        cycle = curr :: cycle
      }
      Some(cycle.last +: cycle)
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

  def topologicalSort(): List[N] = topologicalSortMemo

  private lazy val topologicalSortMemo = computeTopologicalSort()

  private def computeTopologicalSort(): List[N] = {

    val terminationTimes = new Array[Any](vertices.size)
    var time = 0
    val workstack = mutable.Stack.empty[(Option[N], Iterator[N])]
    val started = mutable.Set.empty[N]

    // DFS
    workstack.push(None -> vertices.iterator)
    while (workstack.nonEmpty) {
      val (currOpt, iter) = workstack.head
      currOpt.foreach(started.add)
      if (iter.hasNext) {
        val next = iter.next()
        if (!started(next)) {
          workstack.push(Some(next) -> adjSetOf(next).iterator)
        }
      } else {
        currOpt.foreach { curr =>
          terminationTimes(time) = curr
          time += 1
        }
        workstack.pop()
      }
    }

    var ls = List.empty[N]
    for (n <- terminationTimes) {
      ls = n.asInstanceOf[N] :: ls
    }
    ls
  }

  def sccs(): Set[Set[N]] = sccsMemo

  private lazy val sccsMemo = computeSCCs()

  private def computeSCCs(): Set[Set[N]] = {
    // Tarjan's algorithm

    val discoveryTimes = mutable.Map.empty[N, Int]
    val lowLinks = mutable.Map.empty[N, Int]
    val sccsStack = mutable.Stack.empty[N]
    val onSccsStack = mutable.Set.empty[N]
    var time = 0
    val sccsB = Set.newBuilder[Set[N]]

    def open(n: N): Unit = {
      discoveryTimes(n) = time
      lowLinks(n) = time
      onSccsStack(n) = true
      time += 1
      sccsStack.push(n)
    }

    def closeVertex(n: N): Unit = {
      if (lowLinks(n) == discoveryTimes(n)) {
        val sccB = Set.newBuilder[N]
        var found = false
        while (!found && sccsStack.nonEmpty) {
          val p = sccsStack.pop()
          onSccsStack(p) = false
          sccB.addOne(p)
          found = (p == n)
        }
        sccsB.addOne(sccB.result())
      }
    }

    class StackFrame private(val parent: N, children: Iterator[N], val prevFrameOpt: Option[StackFrame]) {

      def this(parent: N, grandParentOpt: Option[StackFrame]) = {
        this(parent, adjSetOf(parent).iterator, grandParentOpt)
      }

      export children.hasNext as hasNextChild
      export children.next as nextChild

      override def toString: String = s"[$parent, hasNextChild:${children.hasNext}, " +
        s"${prevFrameOpt.map(_ => "<non-root>").getOrElse("<root>")}]"
    }

    for (root <- vertices) {
      if (!discoveryTimes.contains(root)) {
        var currFrame = StackFrame(root, None)
        open(root)
        var endDFS = false
        while (!endDFS) {
          while (currFrame.hasNextChild) {
            val child = currFrame.nextChild()
            if (onSccsStack(child)) {
              lowLinks(currFrame.parent) = Math.min(lowLinks(currFrame.parent), discoveryTimes(child))
            } else if (!discoveryTimes.contains(child)) {
              currFrame = StackFrame(child, Some(currFrame))
              open(child)
            }
          }
          closeVertex(currFrame.parent)
          currFrame.prevFrameOpt match {
            case Some(prevFrame) =>
              lowLinks(prevFrame.parent) = Math.min(lowLinks(prevFrame.parent), lowLinks(currFrame.parent))
              currFrame = prevFrame
            case None =>
              endDFS = true
          }
        }
      }
    }
    sccsB.result()
  }

  def sccGraph(): Graph[Set[N]] = {
    val sccGraphB = Graph.Builder[Set[N]]()
    val vertexToScc = mutable.Map.empty[N, Set[N]]
    for (scc <- sccs()) {
      sccGraphB.addVertex(scc)
      for (n <- scc) {
        vertexToScc.addOne(n -> scc)
      }
    }
    for ((from, to) <- edges) {
      val fromScc = vertexToScc(from)
      val toScc = vertexToScc(to)
      if (fromScc != toScc) {
        sccGraphB.addEdge(fromScc, toScc)
      }
    }
    sccGraphB.build()
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

    def addDescendants(n: N, descendants: IterableOnce[N]): this.type = {
      addVertex(n)
      for (d <- descendants) {
        addVertex(d)
      }
      adjSets.apply(n).addAll(descendants)
      this
    }

    def build(): Graph[N] =
      Graph(adjSets.toMap.map((n, as) => n -> as.toSet))

  }

}
