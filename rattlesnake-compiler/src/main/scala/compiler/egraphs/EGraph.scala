package compiler.egraphs

import compiler.egraphs.EGraph.ENodeWrapper
import compiler.irs.SSA.{FieldResolutionTarget, InvocationTarget}
import compiler.lang.Formulas
import compiler.lang.Formulas.Formula

import scala.collection.SeqMap
import scala.collection.immutable.TreeSet


final class EGraph private(
                            val classes: SeqMap[EClassId, EClass],
                            ownerArgs: SeqMap[ENode, EClass]
                          )(using classIdGen: EClassId.Generator) {
  private val owners: SeqMap[ENodeWrapper, EClass] = for ((n, cl) <- ownerArgs) yield ENodeWrapper(n, this) -> cl

  /*
   * TODO optimize?
   * Optimization ideas:
   *  - pool of ENodeWrappers
   *  - collections created by map in eEquals and eHashCode
   */

  def areEqual(clId1: EClassId, clId2: EClassId): Boolean =
    classes(clId1) == classes(clId2)

  def areEqual(n1: ENode, n2: ENode): Boolean = (findOwner(n1), findOwner(n2)) match {
    case (Some(cl1), Some(cl2)) => cl1 == cl2
    case _ => false
  }

  def areEqual(f1: Formula, f2: Formula): (EGraph, Boolean) = {
    val (ig1, f1Id) = this.withFormulaAbsorbed(f1)
    val (ig2, f2Id) = ig1.withFormulaAbsorbed(f2)
    (ig2, ig2.areEqual(f1Id, f2Id))
  }

  def nodeAdded(n: ENode): (EGraph, EClassId) = {
    val wr = owners.get(ENodeWrapper(n, this))
    wr match {
      case Some(eClass) => (this, eClass.canonicalId)
      case None =>
        val newClassId = classIdGen.next()
        val newClass = EClass(Set(n), TreeSet(newClassId), newClassId)
        val newGraph = EGraph(
          classes ++ SeqMap(newClassId -> newClass),
          unwrappedOwners ++ SeqMap(n -> newClass)
        )
        (newGraph, newClassId)
    }
  }

  def withEquality(n1: ENode, n2: ENode): EGraph = (findOwner(n1), findOwner(n2)) match {
    case (Some(cl1), Some(cl2)) if cl1 == cl2 => this
    case (Some(cl1), Some(cl2)) =>
      withEquality(cl1, cl2)
    case (Some(clId1), None) =>
      copyWithNewNodeInEClass(clId1, n2)
    case (None, Some(clId2)) =>
      copyWithNewNodeInEClass(clId2, n1)
    case (None, None) =>
      val newClassId = classIdGen.next()
      val newClass = EClass(Set(n1, n2), TreeSet(newClassId), newClassId)
      EGraph(SeqMap(newClassId -> newClass), SeqMap(n1 -> newClass, n2 -> newClass))
  }

  def withEquality(clId1: EClassId, clId2: EClassId): EGraph =
    withEquality(classes(clId1), classes(clId2))

  def withEquality(f1: Formula, f2: Formula): EGraph = {
    val (ig1, f1ClId) = this.withFormulaAbsorbed(f1)
    val (ig2, f2ClId) = ig1.withFormulaAbsorbed(f2)
    ig2.withEquality(f1ClId, f2ClId)
  }

  private def withEquality(cl1: EClass, cl2: EClass): EGraph =
    if cl1 == cl2 then this
    else {
      val mergedClass = EClass(cl1.nodes ++ cl2.nodes, cl1.idAliases ++ cl2.idAliases, cl1.canonicalId)
      val newClasses = for ((clId, cl) <- classes) yield clId -> (if mergedClass.idAliases.contains(clId) then mergedClass else cl)
      val newOwners = for ((w, cl) <- owners) yield w.eNode -> (if cl == cl1 || cl == cl2 then mergedClass else cl)
      EGraph(newClasses, newOwners)
    }

  /**
   * @return (id, egraph) where id is the id of the eclass in egraph that the result of the formula belongs to
   */
  def withFormulaAbsorbed(f: Formula): (EGraph, EClassId) = f match {
    case value: Formulas.IdValue => nodeAdded(EIdValNode(value))
    case cst: Formulas.ConstFormula => nodeAdded(EConstNode(cst.value))
    case Formulas.Select(owner, FieldResolutionTarget.Resolved(receiverSig, fieldId)) if receiverSig.fields(fieldId).isStable =>
      val (ig, ownerClId) = this.withFormulaAbsorbed(owner)
      ig.nodeAdded(ESelectNode(ownerClId, fieldId))
    case _: Formulas.Select => throw IllegalArgumentException("selects can be converted to an e-node only if the field is resolved and stable")
    case Formulas.Call(receiver, InvocationTarget.Resolved(funSig), args) =>
      val (rg, rid) = this.withFormulaAbsorbed(receiver)
      val (ag, argIds) = rg.withFormulasAbsorbed(args)
      ag.nodeAdded(ECallNode(rid, funSig.functionName, argIds))
    case _: Formulas.Call =>
      // NOTE: this does NOT take into account the possible side effects of the call
      throw IllegalArgumentException("calls can be converted to an e-node only if they have been resolved")
    case Formulas.Sum(terms) =>
      val (tg, termIds) = this.withFormulasAbsorbed(terms)
      tg.nodeAdded(EPlusNode(termIds.toSet))
    case Formulas.Neg(operand) =>
      val (og, operandId) = this.withFormulaAbsorbed(operand)
      og.nodeAdded(ENegNode(operandId))
    case Formulas.Times(terms) =>
      val (tg, termIds) = this.withFormulasAbsorbed(terms)
      tg.nodeAdded(ETimesNode(termIds.toSet))
    case Formulas.DivBy(lhs, rhs) =>
      val (lg, lid) = this.withFormulaAbsorbed(lhs)
      val (rg, rid) = lg.withFormulaAbsorbed(rhs)
      rg.nodeAdded(EDivNode(lid, rid))
    case Formulas.Modulo(lhs, rhs) =>
      val (lg, lid) = this.withFormulaAbsorbed(lhs)
      val (rg, rid) = lg.withFormulaAbsorbed(rhs)
      rg.nodeAdded(EModuloNode(lid, rid))
  }

  private def withFormulasAbsorbed(formulas: Iterable[Formula]): (EGraph, List[EClassId]) = {
    val formulaIdsB = List.newBuilder[EClassId]
    var ig = this
    for (f <- formulas) {
      val (newIg, formulaId) = ig.withFormulaAbsorbed(f)
      formulaIdsB.addOne(formulaId)
      ig = newIg
    }
    (ig, formulaIdsB.result())
  }

  private def copyWithNewNodeInEClass(origCl: EClass, n: ENode): EGraph = {
    val augmentedCl = EClass(origCl.nodes + n, origCl.idAliases, origCl.canonicalId)
    val newClasses = for ((clId, cl) <- classes) yield clId -> (if cl == origCl then augmentedCl else cl)
    val newOwners = (for ((w, cl) <- owners) yield w.eNode -> (if cl == origCl then augmentedCl else cl)) ++ SeqMap(n -> augmentedCl)
    EGraph(newClasses, newOwners)
  }

  private def unwrappedOwners: SeqMap[ENode, EClass] = for ((wr, cl) <- owners) yield wr.eNode -> cl

  private def findOwner(n: ENode): Option[EClass] = owners.get(ENodeWrapper(n, this))

  override def equals(that: Any): Boolean = throw UnsupportedOperationException()

  override def hashCode(): Int = throw UnsupportedOperationException()

  override def toString: String = {
    val indent = "   "
    val sb = StringBuilder("EGraph {\n")
    for (cl <- classes.values.toList.distinct) {
      sb.append(indent)
        .append(cl.idAliases.map(id => if id == cl.canonicalId then s"$id*" else id.toString).mkString(","))
        .append(" -> ")
        .append(cl.nodes.mkString("{ ", ", ", " }"))
        .append("\n")
    }
    sb.append("}")
    sb.toString
  }
}

object EGraph {

  def empty(using EClassId.Generator): EGraph = EGraph(SeqMap.empty, SeqMap.empty)

  private final class ENodeWrapper(val eNode: ENode, private val eGraph: EGraph) {

    override def equals(that: Any): Boolean = {
      that match {
        case that: ENodeWrapper =>
          require(this.eGraph eq that.eGraph)
          this.eNode.eEquals(that.eNode)(using eGraph.classes(_))
        case _ => false
      }
    }

    override def hashCode(): Int = eNode.eHashCode()(using eGraph.classes(_))
  }

  type ClassRetriever = EClassId => EClass

}
