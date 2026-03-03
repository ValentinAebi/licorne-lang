package compiler.egraphs

import compiler.egraphs.EGraph.ClassRetriever
import compiler.identifiers.FunOrVarId
import compiler.lang.Formulas.IdValue
import compiler.lang.Operator

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
}

final case class EIdValNode(idValue: IdValue) extends ENode {

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case EIdValNode(thatIdValue) => this.idValue == thatIdValue
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int = Objects.hash(idValue)
}

final class EIntermediateNode extends ENode {
  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = this eq that

  override def eHashCode()(using findClass: ClassRetriever): Int = System.identityHashCode(this)
}

final case class ESelectNode(owner: EClassId, fieldId: FunOrVarId) extends ENode {

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case ESelectNode(thatOwner, thatFieldId) => this.fieldId == thatFieldId && findClass(this.owner) == findClass(thatOwner)
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int =
    Objects.hash(fieldId, findClass(owner))

}

final case class ECallNode(receiver: EClassId, funId: FunOrVarId, args: List[EClassId]) extends ENode {

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case ECallNode(thatReceiver, thatFunId, thatArgs) =>
      this.funId == thatFunId && findClass(this.receiver) == findClass(thatReceiver) && inOrderEqual(this.args, thatArgs, findClass)
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int =
    Objects.hash(findClass(receiver), funId, args.map(findClass))
}

sealed trait OperatorENode(val op: Operator) extends ENode {

  /**
   * @return a set if the operation is commutative, a sequence otherwise
   */
  def operands: Iterable[EClassId]

  override def eEquals(that: ENode)(using findClass: ClassRetriever): Boolean = that match {
    case that: OperatorENode if this.op == that.op =>
      require(this.operands.size == that.operands.size)
      this.operands.map(findClass) == that.operands.map(findClass)
    case _ => false
  }

  override def eHashCode()(using findClass: ClassRetriever): Int =
    Objects.hash(op, operands.map(findClass))
}

final class EPlusNode(val operands: Set[EClassId]) extends OperatorENode(Operator.Plus)

final class ENegNode(operand: EClassId) extends OperatorENode(Operator.Minus) {
  override def operands: Iterable[EClassId] = List(operand)
}

final class ETimesNode(val operands: Set[EClassId]) extends OperatorENode(Operator.Times)

final class EDivNode(lhs: EClassId, rhs: EClassId) extends OperatorENode(Operator.Div) {
  override def operands: Iterable[EClassId] = List(lhs, rhs)
}

final class EModuloNode(lhs: EClassId, rhs: EClassId) extends OperatorENode(Operator.Modulo) {
  override def operands: Iterable[EClassId] = List(lhs, rhs)
}

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
