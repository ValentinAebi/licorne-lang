package compiler.typing.smartcasting.egraphs

import compiler.lang.Formulas
import compiler.lang.Formulas.*
import compiler.lang.Operator.{And as OpAnd, Div as OpDiv, Equality as OpEq, ExclamationMark as OpLogicNeg, LessOrEq as OpLeq, LessThan as OpLt, Minus as OpMinus, Modulo as OpModulo, Or as OpOr, Plus as OpPlus, Times as OpTimes}
import compiler.lang.Types.Type
import compiler.smt.{MeetJoinComputer, Simplifier}
import compiler.typing.contexts.SubtypingContext

import scala.collection.mutable


final class EGraph private() {
  private val nodeToClass = mutable.LinkedHashMap.empty[ENode, EClass.Ref]

  private[egraphs] def getNodeToClassMapping: Iterable[(ENode, EClass.Ref)] = nodeToClass

  private[egraphs] def initNodeToClassMapping(mapping: IterableOnce[(ENode, EClass.Ref)]): Unit = {
    if (this.nodeToClass.nonEmpty) {
      throw new IllegalStateException("e-graph has already been initialized")
    }
    this.nodeToClass.addAll(mapping)
  }

  def classOf(formula: Formula): EClass =
    classRefOf(formula).getTarget

  def deepCopy: EGraph =
    (new EGraphsCopier).copyGraph(this)

  def areEqual(f1: Formula, f2: Formula): Boolean =
    classOf(f1) eq classOf(f2)

  def merge(f1: Formula, f2: Formula)(using Simplifier): Unit = {
    val cl1Ref = classRefOf(f1)
    val cl1 = cl1Ref.getTarget
    val cl2 = classOf(f2)
    if (cl1 eq cl2) {
      return
    }
    val affectedNodes = mutable.ListBuffer.empty[(ENode, EClass.Ref)]
    for {
      ref <- cl2.currentReferencesView
      n <- ref.getNodesWithThisRefAsOperand
    } {
      affectedNodes.addOne(n -> nodeToClass.apply(n))
    }
    for ((n, _) <- affectedNodes) {
      nodeToClass.remove(n)
    }
    for (ref <- cl2.currentReferencesView) {
      ref.setTarget(cl1)
    }
    assert(cl2.currentReferencesView.isEmpty, "unexpected remaining references in merged class")
    for ((n, clRef) <- affectedNodes) {
      nodeToClass.put(n, clRef)
    }
    for (n <- cl2.nodesView) {
      addNodeToClass(n, cl1Ref)
    }
    for (explFormula <- cl2.getExplicitFormulas) {
      cl1.addExplicitFormula(explFormula)
    }
    cl2.getSmartcastType.foreach { tpe =>
      cl1.saveSmartcast(tpe)  // FIXME use return value
    }
  }

  def saveSmartcast(formula: Formula, tpe: Type)(using Simplifier): Option[Type] = {
    classOf(formula).saveSmartcast(tpe)
  }

  def smartcastFor(formula: Formula): Option[Type] =
    classOf(formula).getSmartcastType

  private def classRefOf(formula: Formula): EClass.Ref = {
    val node = encode(formula)
    for (ref <- node.operands) {
      ref.addNodeWithThisRefAsOperand(node)
    }
    val classRef = nodeToClass.get(node) match {
      case Some(classRef) => classRef
      case None => newSingletonClass(node)
    }
    classRef.getTarget.addExplicitFormula(formula)
    classRef
  }

  private def newSingletonClass(n: ENode): EClass.Ref = {
    val clazz = EClass()
    val ref = EClass.Ref(clazz)
    addNodeToClass(n, ref)
    ref
  }

  private def addNodeToClass(n: ENode, clRef: EClass.Ref): Unit = {
    nodeToClass.put(n, clRef)
    clRef.getTarget.addNode(n)
  }

  private def encode(formula: Formula): ENode = formula match {
    case value: IdValue =>
      IdValNode(value)
    case formula: ConstFormula =>
      ConstNode(formula.value)
    case Select(owner, field) =>
      SelectNode(classRefOf(owner), field.fieldId)
    case Call(receiver, func, typeArgs, args) =>
      CallNode(classRefOf(receiver), func.funId, args.map(classRefOf))
    case Plus(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpPlus, classRefOf(rhs))
    case Neg(operand) =>
      UnaryOpNode(OpMinus, classRefOf(operand))
    case Times(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpTimes, classRefOf(rhs))
    case DivBy(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpDiv, classRefOf(rhs))
    case Modulo(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpModulo, classRefOf(rhs))
    case LogicalAnd(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpAnd, classRefOf(rhs))
    case LogicalNot(operand) =>
      UnaryOpNode(OpLogicNeg, classRefOf(operand))
    case LogicalOr(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpOr, classRefOf(rhs))
    case Equality(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpEq, classRefOf(rhs))
    case LessOrEq(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpLeq, classRefOf(rhs))
    case LessThan(lhs, rhs) =>
      BinaryOpNode(classRefOf(lhs), OpLt, classRefOf(rhs))
    case TypePredicate(subject, tpe) =>
      TypePredicateNode(classRefOf(subject), tpe)
  }

}

object EGraph {

  def newEmpty: EGraph = EGraph()

}
