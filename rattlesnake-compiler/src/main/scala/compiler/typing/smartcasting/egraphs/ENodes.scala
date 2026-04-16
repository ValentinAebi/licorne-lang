package compiler.typing.smartcasting.egraphs

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.Formulas.IdValue
import compiler.lang.Operator

sealed trait ENode

final case class IdValNode(idValue: IdValue) extends ENode

final case class ConstNode(cst: Any) extends ENode

final case class UnaryOpNode(op: Operator, operand: EClass.Id) extends ENode

final case class BinaryOpNode(lhs: EClass.Id, op: Operator, rhs: EClass.Id) extends ENode

final case class CallNode(receiver: EClass.Id, funId: FunOrVarId, args: List[EClass.Id]) extends ENode

final case class SelectNode(receiver: EClass.Id, fieldId: FunOrVarId) extends ENode

final case class TypePredicateNode(subject: EClass.Id, tpe: TypeIdentifier) extends ENode
