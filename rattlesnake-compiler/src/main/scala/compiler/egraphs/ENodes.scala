package compiler.egraphs

import compiler.egraphs.EGraph.ClassRetriever
import compiler.identifiers.FunOrVarId
import compiler.lang.Formulas.IdValue
import compiler.lang.Operator
import compiler.util.SeqSet

import java.util.Objects


sealed trait ENode {
  def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean

  def eHashCode()(using findClass: ClassRetriever): Int
}

final case class EConstNode(cst: Any) extends ENode {

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case that: EConstNode => this.cst == that.cst
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int = Objects.hash(cst)

  override def toString: String = cst.toString
}

final case class EIdValNode(idValue: IdValue) extends ENode {

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case EIdValNode(thatIdValue) => this.idValue == thatIdValue
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int = Objects.hash(idValue)

  override def toString: String = idValue.toString
}

final case class ESelectNode(owner: EClassId, fieldId: FunOrVarId) extends ENode {

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case ESelectNode(thatOwner, thatFieldId) => this.fieldId == thatFieldId && findClass(this.owner) == findClass(thatOwner)
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int =
    Objects.hash(fieldId, findClass(owner))

  override def toString: String = s"$owner.$fieldId"
}

final case class ECallNode(receiver: EClassId, funId: FunOrVarId, args: List[EClassId]) extends ENode {

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case ECallNode(thatReceiver, thatFunId, thatArgs) =>
      this.funId == thatFunId && findClass(this.receiver) == findClass(thatReceiver) && inOrderEqual(this.args, thatArgs, findClass)
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int =
    Objects.hash(findClass(receiver), funId, args.map(findClass))

  override def toString: String = s"$receiver.$funId" ++ args.mkString("(", ",", ")")
}

sealed trait BinaryOperatorENode(val op: Operator, isCommutative: Boolean) extends ENode {

  val lhs: EClassId
  val rhs: EClassId

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case that: BinaryOperatorENode if this.op == that.op =>
      val thisLhsClass = findClass(this.lhs)
      val thisRhsClass = findClass(this.rhs)
      val thatLhsClass = findClass(that.lhs)
      val thatRhsClass = findClass(that.rhs)
      (thisLhsClass == thatLhsClass && thisRhsClass == thatRhsClass) ||
        (isCommutative && thisLhsClass == thatRhsClass && thisRhsClass == thatLhsClass)
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int =
    Objects.hash(op, findClass(lhs), findClass(rhs))

  override def toString: String = s"$op($lhs,$rhs)"
}

sealed trait UnaryOperatorNode(val op: Operator) extends ENode {
  val operand: EClassId

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case that: UnaryOperatorNode if this.op == that.op =>
      findClass(this.operand) == findClass(that.operand)
  }

  override def eHashCode()(using findClass: ClassRetriever): Int =
    Objects.hash(op, findClass(operand))
}

final case class EPlusNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Plus, isCommutative = true)

final case class ENegNode(operand: EClassId) extends UnaryOperatorNode(Operator.Minus)

final case class ETimesNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Times, isCommutative = true)

final case class EDivNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Div, isCommutative = false)

final case class EModuloNode(lhs: EClassId, rhs: EClassId) extends BinaryOperatorENode(Operator.Modulo, isCommutative = false)

private def inOrderEqual(l: Iterable[EClassId], r: Iterable[EClassId], findClass: ClassRetriever): Boolean =
  if l.size != r.size then false
  else {
    val itL = l.iterator
    val itR = r.iterator
    while (itL.hasNext) {
      if (findClass(itL.next()) != findClass(itR.next())) {
        return false
      }
    }
    true
  }
