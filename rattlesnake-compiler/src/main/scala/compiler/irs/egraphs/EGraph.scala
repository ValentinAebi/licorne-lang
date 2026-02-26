package compiler.irs.egraphs

import compiler.irs.ssa.SSA.IdValue
import EGraph.ApproxMode
import compiler.lang.Operator
import compiler.util.SeqSet

import scala.collection.mutable
import scala.util.boundary


final class EGraph private(private val gen: EClassId.Generator) {

  private val classes = mutable.LinkedHashMap.empty[EClassId, EClass]

  // maps every node to itself, see the classOf method.
  // WARNING: use with care, ENodes are mutable and equals and hashCode are not stable!
  private val nodes = mutable.LinkedHashMap.empty[ENode, ENode]

  private val nodesMentioning = mutable.LinkedHashMap.empty[EClassId, mutable.LinkedHashSet[ENode]]

  private val trueClassId: EClassId = classOf(TrueNode)
  private val falseClassId: EClassId = classOf(FalseNode)

  def deepCopy: EGraph = {
    val newGraph = EGraph(gen)
    for ((clId, oldCl) <- this.classes) {
      val newCl =
        if oldCl.containsNode(TrueNode) then newGraph.classes(newGraph.trueClassId)
        else if oldCl.containsNode(FalseNode) then newGraph.classes(newGraph.falseClassId)
        else EClass(newGraph)
      oldCl.copyTypingDataTo(newCl)
      newGraph.classes.put(clId, newCl)
    }
    for ((_, n) <- nodes) {
      val clId = n.classId
      val newNode = n.copy
      newGraph.nodes.put(newNode, newNode)
      newGraph.classes(clId).addNode(newNode)
      newGraph.saveChildrenMentions(newNode)
    }
    newGraph
  }

  def classOf(extNode: ENode): EClassId = {
    /* nodes maps every node to itself.
     * This way, given a node, one can retrieve the internal version of it 
     * (which contains the pointer to the e-class, ignored by the == method). */
    nodes.get(extNode) match {
      case Some(inNode) => inNode.classId
      case None =>
        nodes.put(extNode, extNode)
        val newClassId = gen.next()
        classAdd(newClassId, extNode)
        saveChildrenMentions(extNode)
        newClassId
    }
  }

  def isProvablyInconsistent: Boolean = areEqual(TrueNode, FalseNode)

  def areEqual(id1: EClassId, id2: EClassId): Boolean = (classes.get(id1), classes.get(id2)) match {
    case (Some(cl1), Some(cl2)) => cl1 == cl2
    case _ => false
  }

  def areEqual(node1: ENode, node2: ENode): Boolean =
    areEqual(classOf(node1), classOf(node2))

  def unify(node1: ENode, node2: ENode): Unit = {
    val class1Id = classOf(node1)
    val class2Id = classOf(node2)
    val class1 = classes(class1Id)
    val class2 = classes(class2Id)
    if (class1.hasDisequality(class2Id) || class2.hasDisequality(class1Id)) {
      mkInconsistent()
    } else if (class1 != class2) {
      val nodesToTransfer = classes.remove(class2Id) match {
        case Some(clazz) => clazz.currentNodes
        case None => Set.empty[ENode]
      }
      for (node <- nodesToTransfer) {
        classAdd(class1Id, node)
      }
      val mentioningNodes = nodesMentioning.remove(class2Id).getOrElse(Set.empty[ENode])
      for (node <- mentioningNodes) {
        nodes.remove(node)
        node.subst(target = class2Id, repl = class1Id)
        nodes.put(node, node)
        saveChildrenMentions(node)
      }
      class2.copyTypingDataTo(class1)
    }
  }

  def saveDisequality(node1: ENode, node2: ENode): Unit = {
    val cl1Id = classOf(node1)
    val cl2Id = classOf(node2)
    if (areEqual(cl1Id, cl2Id)) {
      mkInconsistent()
    } else {
      val cl1 = classes(cl1Id)
      val cl2 = classes(cl2Id)
      cl1.saveDisequality(cl2Id)
      cl2.saveDisequality(cl1Id)
    }
  }

  def saveLessOrEq(left: ENode, right: ENode): Unit = {
    val leftClassId = classOf(left)
    val rightClassId = classOf(right)
    val leftClass = classes(leftClassId)
    val rightClass = classes(rightClassId)
    leftClass.saveUpperBound(rightClassId)
    rightClass.saveLowerBound(leftClassId)
  }

  def equalitySaturation(): Unit = ???

  def asConst(classId: EClassId): Option[ConstNode] = classes(classId).asConst

  def repr(classId: EClassId, maxDepth: Int, approxMode: ApproxMode): Option[ENode] = boundary {
    val clazz = classes(classId)
    ???
  }

  private def classAdd(clazz: EClassId, node: ENode): Unit = {
    node.classId = clazz
    val addIsValid = classes.getOrElseUpdate(clazz, EClass(this)).addNode(node)
    if (!addIsValid) {
      mkInconsistent()
    }
  }

  private def saveChildrenMentions(node: ENode): Unit = {
    for (childId <- node.children) {
      nodesMentioning.getOrElseUpdate(childId, mutable.LinkedHashSet.empty).add(node)
    }
  }

  private def mkInconsistent(): Unit = {
    unify(TrueNode, FalseNode)
  }

}

object EGraph {

  def newEmpty: EGraph = new EGraph(EClassId.Generator())

  enum ApproxMode {
    case DefaultToUpperBound
    case DefaultToLowerBound
    case ExactOnly
  }

}
