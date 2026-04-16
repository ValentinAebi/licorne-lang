package compiler.typing.smartcasting.egraphs

import compiler.lang.{Formulas, Operator}
import compiler.lang.Formulas.*
import compiler.lang.Operator.{And as OpAnd, Div as OpDiv, Equality as OpEq, ExclamationMark as OpLogicNeg, LessOrEq as OpLeq, LessThan as OpLt, Minus as OpMinus, Modulo as OpModulo, Or as OpOr, Plus as OpPlus, Times as OpTimes}
import compiler.lang.Types.Type
import compiler.typing.MeetJoinComputer
import compiler.util.SeqSet

import scala.collection.mutable

final class EGraph private {
  private val idToClass = mutable.LinkedHashMap.empty[EClass.Id, EClass]
  private val nodeToClassId = mutable.LinkedHashMap.empty[ENode, EClass.Id]
  
  def classOfId(id: EClass.Id): EClass =
    idToClass.apply(id)

  def deepCopy: EGraph = {
    val copy = EGraph()
    for ((id, cl) <- idToClass) {
      copy.idToClass.put(id, cl.deepCopy)
    }
    copy.nodeToClassId.addAll(this.nodeToClassId)
    copy
  }

  def classOf(formula: Formula): EClass = {
    val id = classIdOf(formula)
    classOfId(id)
  }

  def classIdOf(formula: Formula): EClass.Id = {
    val node = encode(formula)
    val id = nodeToClassId.get(node) match {
      case Some(classId) => classId
      case None => newClass(node)
    }
    classOfId(id).addExplicitFormula(formula)
    id
  }

  def areEqual(f1: Formula, f2: Formula): Boolean =
    classOf(f1) == classOf(f2)

  def areEqual(clId1: EClass.Id, clId2: EClass.Id): Boolean =
    classOfId(clId1) == classOfId(clId2)

  def merge(f1: Formula, f2: Formula): Unit = {
    val cl1Id = classIdOf(f1)
    val cl2Id = classIdOf(f2)
    merge(cl1Id, cl2Id)
  }

  def merge(cl1Id: EClass.Id, cl2Id: EClass.Id): Unit = {
    if (cl1Id == cl2Id) {
      return
    }
    val cl1 = classOfId(cl1Id)
    val cl2 = classOfId(cl2Id)
    if (cl1 == cl2) {
      return
    }
    for (n <- cl2.nodesView) {
      addNodeToClass(n, cl1Id)
    }
    for (f <- cl2.explicitFormulasView) {
      cl1.addExplicitFormula(f)
    }
  }

  def saveSmartcast(formula: Formula, tpe: Type)(using MeetJoinComputer): Option[Type] = {
    classOf(formula).saveSmartcast(tpe)
  }

  def smartcastFor(formula: Formula): Option[Type] = classOf(formula).getSmartcast

  private def encode(formula: Formula): ENode = formula match {
    case value: IdValue =>
      IdValNode(value)
    case formula: ConstFormula =>
      ConstNode(formula.value)
    case Select(owner, field) =>
      SelectNode(classIdOf(owner), field.fieldId)
    case Call(receiver, func, typeArgs, args) =>
      CallNode(classIdOf(receiver), func.funId, args.map(classIdOf))
    case Plus(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpPlus, classIdOf(rhs))
    case Neg(operand) =>
      UnaryOpNode(OpMinus, classIdOf(operand))
    case Times(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpTimes, classIdOf(rhs))
    case DivBy(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpDiv, classIdOf(rhs))
    case Modulo(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpModulo, classIdOf(rhs))
    case LogicalAnd(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpAnd, classIdOf(rhs))
    case LogicalNot(operand) =>
      UnaryOpNode(OpLogicNeg, classIdOf(operand))
    case LogicalOr(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpOr, classIdOf(rhs))
    case Equality(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpEq, classIdOf(rhs))
    case LessOrEq(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpLeq, classIdOf(rhs))
    case LessThan(lhs, rhs) =>
      BinaryOpNode(classIdOf(lhs), OpLt, classIdOf(rhs))
    case TypePredicate(subject, tpe) =>
      TypePredicateNode(classIdOf(subject), tpe)
  }

  private def newClass(nodes: ENode*): EClass.Id = {
    val clazzId = new EClass.Id
    val clazz = EClass()
    idToClass.put(clazzId, clazz)
    for (node <- nodes) {
      addNodeToClass(node, clazzId)
    }
    clazzId
  }

  private def addNodeToClass(node: ENode, classId: EClass.Id, isRecursiveCommutAdd: Boolean = false): Unit = {
    nodeToClassId.put(node, classId)
    classOfId(classId).addNode(node)
    node match {
      case BinaryOpNode(lhs, op, rhs) if !isRecursiveCommutAdd && op.isCommutative =>
        val commutNode = BinaryOpNode(rhs, op, lhs)
        if (!nodeToClassId.contains(commutNode)) {
          addNodeToClass(commutNode, classId, isRecursiveCommutAdd = true)
        }
      case _ => ()
    }
  }

}

object EGraph {

  def newEmpty: EGraph = EGraph()

}
