package compiler.datastructures

import org.junit.Assert.{assertEquals, assertTrue}
import org.junit.Test

class GraphTests {

  private val graph1: Graph[Int] = {
    val gb = Graph.Builder[Int]()

    extension (from: Int) def ->(to: Int): Unit = {
      gb.addEdge(from, to)
    }

    /*
     1 -> 2 <- 8 <- 7 -> 9 <- 11     15
     v    v         ^ ^. v        v"  v
     3 -> 4 -> 5 -> 6    10 <- 12 <- 13 -> 14
     */

    // SCCs: {1}, {3}, {2,4,5,6,7,8,9,10}, {11}, {12}, {13}, {14}, {15}

    1 -> 2
    1 -> 3
    2 -> 4
    3 -> 4
    4 -> 5
    5 -> 6
    6 -> 7
    7 -> 8
    7 -> 9
    8 -> 2
    9 -> 10
    10 -> 7
    11 -> 9
    12 -> 10
    13 -> 12
    13 -> 14
    15 -> 12
    15 -> 13

    gb.build()
  }

  private val graph2: Graph[String] = {
    val gb = Graph.Builder[String]()

    extension (from: String) def ->(to: String): Unit = {
      gb.addEdge(from, to)
    }

    /*
     A -> B <- H <- G -> I <- K <- P <- O
     v    v         ^    v              ^
     C -> D -> E -> F    J -> L -> M -> N
     */

    // SCCs: {A}, {B,D,E,F,G,H}, {C}, {I,J,L,M,N,O,P,K}

    "A" -> "B"
    "A" -> "C"
    "B" -> "D"
    "C" -> "D"
    "D" -> "E"
    "E" -> "F"
    "F" -> "G"
    "G" -> "H"
    "G" -> "I"
    "H" -> "B"
    "I" -> "J"
    "J" -> "L"
    "K" -> "I"
    "L" -> "M"
    "M" -> "N"
    "N" -> "O"
    "O" -> "P"
    "P" -> "K"

    gb.build()
  }

  private val graph3: Graph[String] = {
    val gb = Graph.Builder[String]()

    extension (from: String) def ->(to: String): Unit = {
      gb.addEdge(from, to)
    }

    /*
     A -> B -> C -> D -> I
     v         v      v"
     E -> F -> G -> H
     */

    "A" -> "B"
    "A" -> "E"
    "B" -> "C"
    "C" -> "D"
    "C" -> "G"
    "D" -> "I"
    "E" -> "F"
    "F" -> "G"
    "G" -> "H"
    "I" -> "H"

    gb.build()
  }

  @Test def findShortestCycleTest1(): Unit = {
    val acceptableSolutions = rotationsOf(7, 9, 10)
    val res = graph1.findShortestCycle().get
    assertTrue(s"incorrect: $res", acceptableSolutions.contains(res))
  }

  @Test def findShortestCycleTest2(): Unit = {
    val acceptableSolutions = rotationsOf("B", "D", "E", "F", "G", "H")
    val res = graph2.findShortestCycle().get
    assertTrue(s"incorrect: $res", acceptableSolutions.contains(res))
  }

  @Test def findShortestPathTest(): Unit = {
    val exp = Seq(15, 12, 10, 7, 8)
    val act = graph1.shortestPath(15, 8).get
    assertEquals(exp, act)
  }

  @Test def topologicalSortTest(): Unit = {
    val result = graph3.topologicalSort()
    assertEquals(graph3.vertices, result.toSet)
    assertEquals(graph3.vertices.size, result.size)
    for (from <- graph3.vertices) {
      val fromIdx = result.indexOf(from)
      for (to <- graph3.adjSetOf(from)) {
        val toIdx = result.indexOf(to)
        assertTrue(s"edge from $from to $to but topological order says $result", fromIdx <= toIdx)
      }
    }
  }

  @Test def sccsTest1(): Unit = {
    val exp = Set(Set(1), Set(3), Set(2, 4, 5, 6, 7, 8, 9, 10), Set(11), Set(12), Set(13), Set(14), Set(15))
    val act = graph1.sccs()
    assertEquals(exp, act)
  }

  @Test def sccsTest2(): Unit = {
    val exp = Set(Set("A"), Set("B", "D", "E", "F", "G", "H"), Set("C"), Set("I", "J", "L", "M", "N", "O", "P", "K"))
    val act = graph2.sccs()
    assertEquals(exp, act)
  }

  @Test def sccsTest3(): Unit = {
    val exp = "ABCDEFGHI".toSet.map(c => Set(c.toString))
    val act = graph3.sccs()
    assertEquals(exp, act)
  }

  private def rotationsOf[T](seq: T*): Set[Seq[T]] = {
    (for (i <- seq.indices) yield {
      val (left, right) = seq.splitAt(i)
      right ++ left :+ right.head
    }).toSet
  }

}
