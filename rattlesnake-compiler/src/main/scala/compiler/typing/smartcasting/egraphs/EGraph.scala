package compiler.typing.smartcasting.egraphs

import compiler.lang.Formulas.*
import compiler.lang.Operator.{And as OpAnd, Div as OpDiv, Equality as OpEq, ExclamationMark as OpLogicNeg, LessOrEq as OpLeq, LessThan as OpLt, Minus as OpMinus, Modulo as OpModulo, Or as OpOr, Plus as OpPlus, Times as OpTimes}
import compiler.lang.Types.Type
import compiler.smt.Simplifier
import compiler.valproxies.ProxyStore

import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable


final class EGraph private[egraphs](startClId: Long) {

  private val clUidGen = AtomicLong(startClId)

  private val classesUf = mutable.Map.empty[EClass, EClass]
  private var nodeToClass = mutable.Map.empty[ENode, EClass]

  private[egraphs] def currentClId: Long = clUidGen.get()

  private[egraphs] def initializeWith(classesUf: IterableOnce[(EClass, EClass)], nodeToClass: IterableOnce[(ENode, EClass)]): Unit = {
    if (this.classesUf.nonEmpty || this.nodeToClass.nonEmpty) {
      throw new AssertionError("e-graph is not empty")
    }
    this.classesUf.addAll(classesUf)
    this.nodeToClass.addAll(nodeToClass)
  }

  private[egraphs] def uf: IterableOnce[(EClass, EClass)] = classesUf

  private[egraphs] def nodeToClassMap: IterableOnce[(ENode, EClass)] = nodeToClass

  def deepCopy: EGraph = EGraphCopier.copyOf(this)

  def areEqual(f1: Formula, f2: Formula): Boolean =
    classOf(f1) eq classOf(f2)

  def merge(f1: Formula, f2: Formula)(using ProxyStore, Simplifier): Unit = {
    doMerge(f1, f2, recurseOnProxies = true)
  }

  private def doMerge(f1: Formula, f2: Formula, recurseOnProxies: Boolean)(using proxyStore: ProxyStore, simplifier: Simplifier): Unit = {
    val cl1 = classOf(f1)
    val cl2 = classOf(f2)
    merge(cl1, cl2)
    if (recurseOnProxies) {
      mergeWithProxy(f1)
      mergeWithProxy(f2)
    }
  }

  private def mergeWithProxy(f: Formula)(using proxyStore: ProxyStore, simplifier: Simplifier): Unit = {
    proxyStore.getProxyIfIdValue(f) match {
      case Some(proxy) if proxy != f && proxy.isPure =>
        doMerge(f, proxy, recurseOnProxies = false)
      case _ => ()
    }
  }

  private def merge(cl1: EClass, cl2: EClass)(using Simplifier): Unit = {
    if (cl1 == cl2) {
      return
    }
    classesUf.put(cl2, cl1)
    for (n <- cl2.nodesView) {
      addNodeToClass(n, cl1)
    }
    cl2.getSmartcastType.foreach { tpe =>
      cl1.saveSmartcast(tpe)
    }
    cl1.addExplicitFormulas(cl2.explicitFormulasView)
    val newNodeToClass = mutable.Map.empty[ENode, EClass]
    val congruences = mutable.ListBuffer.empty[(EClass, EClass)]
    for ((n, cl) <- nodeToClass) {
      canonicalize(n)
      newNodeToClass.get(n) match {
        case Some(otherCl) =>
          congruences.addOne(cl, otherCl)
        case None =>
          newNodeToClass.put(n, canonicalize(cl))
      }
    }
    nodeToClass = newNodeToClass
    for ((cl1, cl2) <- congruences) {
      merge(cl1, cl2)
    }
  }

  def saveSmartcast(formula: Formula, tpe: Type)(using simplifier: Simplifier): Unit =
    classOf(formula).saveSmartcast(tpe)
    
  def saveNonNull(formula: Formula): Unit = {
    classOf(formula).markNonNull()
  }

  def smartcastFor(formula: Formula): Option[Type] =
    classOf(formula).getSmartcastType
  
  def isKnownNonNull(formula: Formula): Boolean =
    classOf(formula).isKnownNonNull

  def classOf(formula: Formula): EClass = {
    val node = encode(formula)
    val clazz = nodeToClass.get(node) match {
      case Some(cl) => cl
      case None => newClass(node)
    }
    clazz.addExplicitFormula(formula)
    clazz
  }

  private def newClass(node: ENode): EClass = {
    val clazz = EClass(clUidGen.incrementAndGet())
    addNodeToClass(node, clazz)
    clazz
  }

  private def addNodeToClass(n: ENode, cl: EClass): Unit = {
    nodeToClass.put(n, cl)
    cl.addNode(n)
  }

  private def encode(formula: Formula): ENode = formula match {
    case value: IdValue =>
      IdValNode(value)
    case formula: ConstFormula =>
      ConstNode(formula.value)
    case Select(owner, field) =>
      SelectNode(classOf(owner), field.fieldId)
    case Call(receiver, func, typeArgs, args) =>
      CallNode(classOf(receiver), func.funId, args.map(classOf))
    case Plus(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpPlus, classOf(rhs))
    case Neg(operand) =>
      UnaryOpNode(OpMinus, classOf(operand))
    case Times(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpTimes, classOf(rhs))
    case DivBy(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpDiv, classOf(rhs))
    case Modulo(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpModulo, classOf(rhs))
    case LogicalAnd(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpAnd, classOf(rhs))
    case LogicalNot(operand) =>
      UnaryOpNode(OpLogicNeg, classOf(operand))
    case LogicalOr(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpOr, classOf(rhs))
    case Equality(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpEq, classOf(rhs))
    case LessOrEq(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpLeq, classOf(rhs))
    case LessThan(lhs, rhs) =>
      BinaryOpNode(classOf(lhs), OpLt, classOf(rhs))
    case TypePredicate(subject, tpe) =>
      TypePredicateNode(classOf(subject), tpe)
  }

  private[egraphs] def canonicalize(n: ENode): Unit = n match {
    case idValNode: IdValNode => ()
    case cstNode: ConstNode => ()
    case unop@UnaryOpNode(op, operand) =>
      unop.operand = canonicalize(operand)
    case binop@BinaryOpNode(lhs, op, rhs) =>
      binop.lhs = canonicalize(lhs)
      binop.rhs = canonicalize(rhs)
    case call@CallNode(receiver, funId, args) =>
      call.receiver = canonicalize(receiver)
      call.args = args.map(canonicalize)
    case sel@SelectNode(receiver, fieldId) =>
      sel.receiver = canonicalize(receiver)
    case tpred@TypePredicateNode(subject, tpe) =>
      tpred.subject = canonicalize(subject)
  }

  private def canonicalize(clazz: EClass): EClass = {
    classesUf.get(clazz) match {
      case Some(dstClass) =>
        val endClass = canonicalize(dstClass)
        classesUf.put(clazz, endClass)
        endClass
      case _ => clazz
    }
  }

  override def toString: String =
    "EGraph {\n" +
      classesUf.map((cl1, cl2) => s"${cl1.shortDescr} -> ${cl2.shortDescr}").mkString("uf = {\n  ", ",\n  ", "\n}").indent(2) +
      nodeToClass.map((n, cl) => s"$n -> ${cl.shortDescr}").mkString("nodes = {\n  ", ",\n  ", "\n}").indent(2) + "}"

}

object EGraph {

  def newEmpty: EGraph = EGraph(-1)

}
