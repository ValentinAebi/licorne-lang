package compiler.egraphs

import compiler.egraphs.CostCache.*

import scala.collection.mutable


final class CostCache(eGraph: EGraph) {
  private val nodeCosts = mutable.Map.empty[ENode, BigInt]
  private val classCosts = mutable.Map.empty[EClass, (ENode, BigInt)]
  private val openClasses = mutable.Set.empty[EClass]

  // TODO check if heuristic really works
  def minCostOf(n: ENode): BigInt = nodeCosts.getOrElseUpdate(n, n match {
    case EConstNode(cst) => 10
    case EIdValNode(idValue) => 20
    case ESelectNode(owner, fieldId) => minCostOf(owner) + 10
    case ECallNode(receiver, funId, args) =>
      minCostOf(receiver) + args.map(minCostOf).sum + 20
    case node: BinaryOperatorENode =>
      2 * minCostOf(node.lhs) + minCostOf(node.rhs) + 20
    case node: UnaryOperatorNode =>
      val opCost = minCostOf(node.operand)
      if opCost <= 20 then opCost + 1 else opCost + 15
  })

  def minCostOf(eClassId: EClassId): BigInt =
    minCostOf(eGraph.classes(eClassId))

  def minCostOf(eClass: EClass): BigInt =
    computeMinNodeInClass(eClass)._2

  def minNodeInClass(eClassId: EClassId): Option[ENode] =
    minNodeInClass(eGraph.classes(eClassId))

  def minNodeInClass(eClass: EClass): Option[ENode] = {
    val (n, cost) = computeMinNodeInClass(eClass)
    Option.when(cost < cycleCost)(n)
  }

  private def computeMinNodeInClass(eClass: EClass): (ENode, BigInt) = {
    if classCosts.contains(eClass) then classCosts(eClass)
    else if openClasses.contains(eClass) then (eClass.nodes.head, cycleCost)
    else {
      openClasses.addOne(eClass)
      val nodesIter = eClass.nodes.iterator
      val firstNode = nodesIter.next()
      var best = (firstNode, minCostOf(firstNode))
      while (nodesIter.hasNext) {
        val currNode = nodesIter.next()
        val currNodeCost = minCostOf(currNode)
        if (currNodeCost < best._2) {
          best = (currNode, currNodeCost)
        }
      }
      openClasses.remove(eClass)
      classCosts.put(eClass, best)
      best
    }
  }

}

object CostCache {

  // TODO maybe find a better solution
  val cycleCost: BigInt = 1_000_000_000L

}
