package compiler.egraphs

import compiler.identifiers.FunOrVarId
import compiler.lang.Formulas.IdValue
import compiler.lang.Operator

import java.util.Objects


sealed trait ENode {
  def operandClassIds: Set[EClassId]
}

final case class EConstNode(cst: Any) extends ENode {

  override def operandClassIds: Set[EClassId] = Set.empty

  override def toString: String = cst.toString
}

final case class EIdValNode(idValue: IdValue) extends ENode {

  override def operandClassIds: Set[EClassId] = Set.empty

  override def toString: String = idValue.toString
}

final case class ESelectNode(owner: EClassId, fieldId: FunOrVarId) extends ENode {

  override def operandClassIds: Set[EClassId] = Set(owner)

  override def toString: String = s"$owner.$fieldId"
}

final case class ECallNode(receiver: EClassId, funId: FunOrVarId, args: List[EClassId]) extends ENode {

  override def operandClassIds: Set[EClassId] = args.toSet + receiver

  override def toString: String = s"$receiver.$funId" ++ args.mkString("(", ",", ")")
}

sealed trait BinaryOperatorENode(val op: Operator, isCommutative: Boolean) extends ENode {

  val lhs: EClassId
  val rhs: EClassId

  override def operandClassIds: Set[EClassId] = Set(lhs, rhs)

  override def toString: String = s"$op($lhs,$rhs)"
}

sealed trait UnaryOperatorNode(val op: Operator) extends ENode {
  val operand: EClassId

  override def operandClassIds: Set[EClassId] = Set(operand)
}

final case class EPlusNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Plus, isCommutative = true)

final case class ENegNode(operand: EClassId) extends UnaryOperatorNode(Operator.Minus) {
  override def toString: String = s"-($operand)"
}

final case class ETimesNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Times, isCommutative = true)

final case class EDivNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Div, isCommutative = false)

final case class EModuloNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Modulo, isCommutative = false)

object ENodes {

  def alreadyInstantiatedNodeClasses: Set[Class[? <: ENode]] = Set(
    classOf[EConstNode],
    classOf[EIdValNode],
    classOf[ESelectNode],
    classOf[ECallNode],
    classOf[EPlusNode],
    classOf[ENegNode],
    classOf[ETimesNode],
    classOf[EDivNode],
    classOf[EModuloNode]
  )

  def alreadyInstantiatedNodeClassesBut(excluded: Class[? <: ENode]*): Set[Class[? <: ENode]] =
    alreadyInstantiatedNodeClassesBut(excluded.toList)

  def alreadyInstantiatedNodeClassesBut(excluded: Iterable[Class[? <: ENode]]): Set[Class[? <: ENode]] =
    alreadyInstantiatedNodeClasses -- excluded

  def alreadyInstantiatedNodeClassesSubtypeOf(superClass: Class[? <: ENode]): Set[Class[? <: ENode]] =
    alreadyInstantiatedNodeClasses.filter(superClass.isAssignableFrom(_))
}
