package compiler.typing.smartcasting.egraphs

import compiler.irs.ssa.Formulas.Formula
import compiler.lang.Types.{IntersectionType, Type}
import compiler.reasoning.Simplifier
import compiler.typing.contexts.TypeParamsContext

import scala.collection.mutable

final class EClass(val uid: Long) {
  private val nodes = mutable.LinkedHashSet.empty[ENode]
  private var smartcastTypeOpt = Option.empty[Type]
  private var nonNullFlag = false
  private val explicitFormulas = mutable.LinkedHashSet.empty[Formula]

  private[egraphs] def initializeWith(nodes: IterableOnce[ENode], smartcastOpt: Option[Type], nonNull: Boolean, formulas: IterableOnce[Formula]): Unit = {
    if (this.nodes.nonEmpty || this.smartcastTypeOpt.nonEmpty || this.explicitFormulas.nonEmpty) {
      throw new AssertionError("e-class is not empty")
    }
    this.nodes.addAll(nodes)
    this.smartcastTypeOpt = smartcastOpt
    this.nonNullFlag = nonNull
    this.explicitFormulas.addAll(formulas)
  }

  def addNode(node: ENode): Unit = {
    nodes.add(node)
  }

  def nodesView: Iterable[ENode] = nodes

  def saveSmartcast(tpe: Type): Unit = {
    val newSmartcast = smartcastTypeOpt match {
      case Some(oldSmartcastType) =>
        IntersectionType(oldSmartcastType, tpe)
      case None => tpe
    }
    smartcastTypeOpt = Some(newSmartcast)
  }
  
  def markNonNull(): Unit = {
    nonNullFlag = true
  }

  def getSmartcastType(using typeParamsCtx: TypeParamsContext, simplifier: Simplifier): Option[Type] =
    smartcastTypeOpt.map(simplifier.simplify)
    
  def getSmartcastTypeNoSimplification: Option[Type] = smartcastTypeOpt
  
  def isKnownNonNull: Boolean = nonNullFlag

  def addExplicitFormula(formula: Formula): Unit = {
    explicitFormulas.add(formula)
  }

  def addExplicitFormulas(formulas: Iterable[Formula]): Unit = {
    explicitFormulas.addAll(formulas)
  }

  def explicitFormulasView: Iterable[Formula] = explicitFormulas
  
  def shortDescr: String = s"*$uid"

}
