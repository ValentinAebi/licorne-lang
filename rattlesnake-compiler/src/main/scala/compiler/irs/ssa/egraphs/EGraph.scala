package compiler.irs.ssa.egraphs

import compiler.irs.ssa.SSA.IdValue
import compiler.lang.Operator
import compiler.util.SeqSet

import scala.collection.mutable
import scala.util.boundary
import scala.util.boundary.Label

final class EGraph(maxRecursiveTransformations: Int = 500) {
  
  private val gen = EClassId.Generator()
  
  private val classes = mutable.LinkedHashMap.empty[EClassId, EClass]
  private val nodes = mutable.LinkedHashMap.empty[ENode, EClassId]
  private val nodesRev = mutable.LinkedHashMap.empty[EClassId, mutable.LinkedHashSet[ENode]]
  
  private val trueClassId: EClassId = classOf(TrueNode)
  private val falseClassId: EClassId = classOf(FalseNode)

  def classOf(node: ENode): EClassId = {
    nodes.getOrElseUpdate(node, {
      val (clazzId, clazz) = newClass()
      clazz.addNode(node)
      nodesRev.getOrElseUpdate(clazzId, mutable.LinkedHashSet.empty).add(node)
      clazzId
    })
  }

  def areEqual(id1: EClassId, id2: EClassId): Boolean = (classes.get(id1), classes.get(id2)) match {
    case (Some(cl1), Some(cl2)) => cl1 == cl2
    case _ => false
  }

  def areEqual(n1: ENode, n2: ENode): Boolean =
    areEqual(classOf(n1), classOf(n2))

  def unify(node1: ENode, node2: ENode): Unit = boundary {
    doUnify(node1, node2)(using new ShortcutCounter)
  }

  def equalitySaturation(): Unit = boundary {
    val shortcutCounter = ShortcutCounter()
    ???
  }

  private def doUnify(node1: ENode, node2: ENode)
                     (using shortcutCounter: ShortcutCounter): Unit = {
    shortcutCounter.check()
    shortcutCounter.decrement()
    val class1Id = classOf(node1)
    val class2Id = classOf(node2)
    val class1 = classes(class1Id)
    val class2 = classes(class2Id)
    if (class1 != class2) {
      class2.deleteAndTransferTo(class1)
      classes(class2Id) = class1
      applyCongruence(class1Id, class2Id)
    }
  }

  private def applyCongruence(id1: EClassId, id2: EClassId)
                             (using shortcutCounter: ShortcutCounter): Unit = {
    shortcutCounter.check()
    val nodes1 = nodesRev(id1)
    val nodes2 = nodesRev(id2)
    if (nodes1.size >= nodes2.size) {
      val nodes2WithSubst = nodes2.map(n => n -> n.subst(id2, id1))
      for {
        n1 <- nodes1
        (n2, n2Subst) <- nodes2WithSubst
        if n1 != n2 && n1 == n2Subst
      } do {
        doUnify(n1, n2)
      }
    } else {
      // optimization: minimize the number of nodes that get substituted
      applyCongruence(id2, id1)
    }
  }

  private def newClass(): (EClassId, EClass) = {
    val clazz = EClass()
    val classId = gen.next()
    classes(classId) = clazz
    (classId, clazz)
  }

  private class ShortcutCounter(using Label[Unit]) {
    private var counter = maxRecursiveTransformations

    def decrement(): Unit = {
      counter -= 1
    }

    def check(): Unit = {
      if (counter <= 0) {
        boundary.break(())
      }
    }

  }

}
