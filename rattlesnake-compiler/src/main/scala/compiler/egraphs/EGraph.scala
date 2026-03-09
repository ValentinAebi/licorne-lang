package compiler.egraphs

import compiler.datastructures.Graph
import compiler.egraphs.rewrites.EqualitySaturationRewriteRule
import compiler.irs.SSA.{FieldResolutionTarget, InvocationTarget}
import compiler.lang.Formulas
import compiler.lang.Formulas.*
import compiler.util.{SeqSet, mapVals}

import scala.collection.immutable.{SeqMap, TreeSet}
import scala.util.boundary


final class EGraph private(
                            classesArgs: SeqMap[EClassId, EClass],
                            ownerArgs: SeqMap[ENode, EClass],
                            upperBounds: SeqMap[EClass, SeqSet[EClass]]
                          )(using classIdGen: EClassId.Generator) {

  val classes: SeqMap[EClassId, EClass] = classesArgs.map { (clId, cl) =>
    clId -> EClass(cl.nodes.map(classesArgs.canonicalize), cl.idAliases, cl.canonicalId)
  }

  private val nodeToClass: SeqMap[ENode, EClass] = for ((n, cl) <- ownerArgs) yield canonicalize(n) -> cl

  private lazy val leqGraph: Graph[EClass] = {
    val gb = Graph.Builder[EClass]()
    for ((cl, lb) <- upperBounds) {
      gb.addDescendants(cl, lb)
    }
    gb.build()
  }

  val costCache: CostCache = CostCache(this)

  def nodeIsWellDefined(n: ENode): Boolean =
    n.operandClassIds.forall(classes.contains)

  def ownerClassOf(n: ENode): EClass =
    findOwner(n).get

  def nodesCnt: Int = nodeToClass.size

  /*
   * TODO optimize?
   * Optimization ideas:
   *  - pool of ENodeWrappers
   *  - collections created by map in eEquals and eHashCode
   */
  def simplified(clId: EClassId, rules: List[EqualitySaturationRewriteRule], maxStepsCnt: Long): Option[Formula] = {
    val ig = afterEqualitySaturation(rules, maxStepsCnt)
    Option.when(ig.costCache.minCostOf(clId) < CostCache.cycleCost)(ig.simplifiedImpl(clId))
  }

  def simplified(n: ENode, rules: List[EqualitySaturationRewriteRule], maxStepsCnt: Long): Option[Formula] = {
    val ig = afterEqualitySaturation(rules, maxStepsCnt)
    Option.when(ig.costCache.minCostOf(n) < CostCache.cycleCost)(ig.simplifiedImpl(n))
  }

  private def simplifiedImpl(clId: EClassId): Formula =
    simplifiedImpl(classes(clId))

  private def simplifiedImpl(n: ENode): Formula = n match {
    case EConstNode(cst: Int) => IntConst(cst)
    case EConstNode(cst: Boolean) => BoolConst(cst)
    case EConstNode(cst: String) => StringConst(cst)
    case EConstNode(cst: Double) => ???
    case EConstNode(cst) =>
      throw new UnsupportedOperationException(s"unexpected constant: $cst")
    case EIdValNode(idValue) => idValue
    case ESelectNode(owner, fieldId) =>
      Select(simplifiedImpl(owner), FieldResolutionTarget.Unresolved(fieldId))
    case ECallNode(receiver, funId, args) =>
      Call(simplifiedImpl(receiver), InvocationTarget.Unresolved(funId), args.map(simplifiedImpl))
    case EPlusNode(lhs, rhs) => Plus(simplifiedImpl(lhs), simplifiedImpl(rhs))
    case ETimesNode(lhs, rhs) => Times(simplifiedImpl(lhs), simplifiedImpl(rhs))
    case EDivNode(lhs, rhs) => DivBy(simplifiedImpl(lhs), simplifiedImpl(rhs))
    case EModuloNode(lhs, rhs) => Modulo(simplifiedImpl(lhs), simplifiedImpl(rhs))
    case ENegNode(operand) => Neg(simplifiedImpl(operand))
  }

  private def simplifiedImpl(cl: EClass): Formula =
    simplifiedImpl(costCache.minNodeInClass(cl).get)

  def equalityQuery(clId1: EClassId, clId2: EClassId): Boolean =
    classes(clId1).canonicalId == classes(clId2).canonicalId

  def equalityQuery(n1: ENode, n2: ENode): Boolean = (findOwner(n1), findOwner(n2)) match {
    case (Some(cl1), Some(cl2)) => cl1 == cl2
    case _ => false
  }

  def equalityQueryNoSaturation(f1: Formula, f2: Formula): (EGraph, Boolean) = {
    val (ig1, f1Id) = this.withFormulaAbsorbed(f1)
    val (ig2, f2Id) = ig1.withFormulaAbsorbed(f2)
    (ig2, ig2.equalityQuery(f1Id, f2Id))
  }

  def equalityQueryAfterSaturation(f1: Formula, f2: Formula, rules: List[EqualitySaturationRewriteRule], maxStepsCnt: Long): (EGraph, Boolean) = {
    val (ig1, f1Id) = this.withFormulaAbsorbed(f1)
    val (ig2, f2Id) = ig1.withFormulaAbsorbed(f2)
    // TODO maybe periodically test equality between rounds of saturation, for performance?
    val satG = ig2.afterEqualitySaturation(rules, maxStepsCnt)
    (satG, satG.equalityQuery(f1Id, f2Id))
  }

  def nodeAdded(n: ENode): (EGraph, EClassId) = {
    require(nodeIsWellDefined(n))
    findOwner(n) match {
      case Some(eClass) =>
        (copyWithNewNodeInEClass(eClass, n), eClass.canonicalId)
      case None =>
        val newClassId = classIdGen.next()
        val newClass = EClass(SeqSet(n), TreeSet(newClassId), newClassId)
        val newGraph = EGraph(
          classes ++ SeqMap(newClassId -> newClass),
          nodeToClass ++ SeqMap(n -> newClass),
          upperBounds
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
      val newClass = EClass(SeqSet(n1, n2), TreeSet(newClassId), newClassId)
      EGraph(
        SeqMap(newClassId -> newClass),
        SeqMap(n1 -> newClass, n2 -> newClass),
        SeqMap.empty
      )
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
      val mergedClass = EClass(cl1.nodes.concat(cl2.nodes), cl1.idAliases ++ cl2.idAliases, cl1.canonicalId)

      def replClass(origClass: EClass) = if origClass == cl1 || origClass == cl2 then mergedClass else origClass

      val newClasses = for ((clId, cl) <- classes) yield clId -> (if mergedClass.idAliases.contains(clId) then mergedClass else cl)
      val newOwners = nodeToClass.mapVals(replClass)
      val newLowerBounds = upperBounds.mapVals(lbs => lbs.map(replClass))
      EGraph(newClasses, newOwners, newLowerBounds)
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
    case Formulas.Plus(lhs, rhs) =>
      val (lg, lid) = this.withFormulaAbsorbed(lhs)
      val (rg, rid) = lg.withFormulaAbsorbed(rhs)
      rg.nodeAdded(EPlusNode(lid, rid))
    case Formulas.Neg(operand) =>
      val (og, operandId) = this.withFormulaAbsorbed(operand)
      og.nodeAdded(ENegNode(operandId))
    case Formulas.Times(lhs, rhs) =>
      val (lg, lid) = this.withFormulaAbsorbed(lhs)
      val (rg, rid) = lg.withFormulaAbsorbed(rhs)
      rg.nodeAdded(ETimesNode(lid, rid))
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
    val nCanonic = canonicalize(n)
    if origCl.nodes.contains(nCanonic) then this
    else {
      val augmentedCl = EClass(origCl.nodes.incl(nCanonic), origCl.idAliases, origCl.canonicalId)

      def replClass(cl: EClass) = if cl == origCl then augmentedCl else cl

      val newClasses = classes.mapVals(replClass)
      val newOwners = nodeToClass.mapVals(replClass) ++ SeqMap(nCanonic -> augmentedCl)
      val newLowerBounds = upperBounds.mapVals(_.map(replClass))
      EGraph(newClasses, newOwners, newLowerBounds)
    }
  }

  def withLessOrEq(l: EClassId, r: EClassId): EGraph =
    withLessOrEq(classes(l), classes(r))

  def withLessOrEq(l: ENode, r: ENode): EGraph =
    withLessOrEq(ownerClassOf(l), ownerClassOf(r))

  def withLessOrEq(l: Formula, r: Formula): EGraph = {
    val (ig1, lid) = this.withFormulaAbsorbed(l)
    val (ig2, rid) = ig1.withFormulaAbsorbed(r)
    ig2.withLessOrEq(lid, rid)
  }

  private def withLessOrEq(l: EClass, r: EClass): EGraph = EGraph(
    classes,
    ownerArgs,
    upperBounds.updatedWith(l) {
      case Some(lbs) => Some(lbs.incl(r))
      case None => Some(SeqSet(r))
    }
  )

  def lessOrEqQuery(l: EClassId, r: EClassId): Boolean =
    lessOrEqQuery(classes(l), classes(r))

  def lessOrEqQuery(l: ENode, r: ENode): Boolean =
    lessOrEqQuery(ownerClassOf(l), ownerClassOf(r))

  def lessOrEqQuery(l: EClass, r: EClass): Boolean =
    l == r || leqGraph.shortestPath(l, r).isDefined

  def lessOrEqQueryNoSaturation(l: Formula, r: Formula): (EGraph, Boolean) = {
    val (ig1, lid) = this.withFormulaAbsorbed(l)
    val (ig2, rid) = ig1.withFormulaAbsorbed(r)
    ig2 -> ig2.lessOrEqQuery(lid, rid)
  }

  def afterEqualitySaturation(rules: List[EqualitySaturationRewriteRule], maxStepsCnt: Long): EGraph = boundary {
    val nodeClassToRules =
      (for r <- rules; nc <- r.nodeTargets yield nc -> r)
        .groupBy(_._1)
        .map((nc, rules) => nc -> rules.map(_._2))
    var stepsCnt = 0L
    var stuck = false
    var eGraph = this
    while (!stuck) {
      stuck = true
      val queue = new java.util.LinkedHashSet[EClass]()
      eGraph.classes.values.foreach(queue.addLast)
      while (!queue.isEmpty) {
        val cl = queue.removeFirst()
        var modified = false
        for {
          n <- cl.nodes
          rule <- nodeClassToRules.getOrElse(n.getClass, Set.empty[EqualitySaturationRewriteRule])
        } do {
          val eGraphAfter = rule.rewrite(eGraph, n, queue)
          if (!(eGraphAfter eq eGraph)) {
            eGraph = eGraphAfter
            modified = true
          }
          stepsCnt += 1
          if (stepsCnt >= maxStepsCnt) {
            boundary.break(eGraph)
          }
        }
      }
    }
    eGraph
  }

  def canonicalize(n: ENode): ENode = classes.canonicalize(n)

  extension (classes: SeqMap[EClassId, EClass]) {

    private def canonicalize(clId: EClassId): EClassId = classes(clId).canonicalId

    private def canonicalize(n: ENode): ENode = n match {
      case constNode: EConstNode => constNode
      case valNode: EIdValNode => valNode
      case ESelectNode(owner, fieldId) =>
        ESelectNode(canonicalize(owner), fieldId)
      case ECallNode(receiver, funId, args) =>
        ECallNode(canonicalize(receiver), funId, args.map(canonicalize))
      case EPlusNode(lhs, rhs) =>
        EPlusNode(canonicalize(lhs), canonicalize(rhs))
      case ETimesNode(lhs, rhs) =>
        ETimesNode(canonicalize(lhs), canonicalize(rhs))
      case EDivNode(lhs, rhs) =>
        EDivNode(canonicalize(lhs), canonicalize(rhs))
      case EModuloNode(lhs, rhs) =>
        EModuloNode(canonicalize(lhs), canonicalize(rhs))
      case ENegNode(operand) =>
        ENegNode(canonicalize(operand))
    }
  }

  private def findOwner(n: ENode): Option[EClass] = nodeToClass.get(canonicalize(n))

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
      for (minNode <- costCache.minNodeInClass(cl)) {
        sb.append("  // ").append(simplifiedImpl(minNode))
      }
      sb.append("\n")
    }
    sb.append("}")
    sb.toString
  }

}

object EGraph {

  def empty(using EClassId.Generator): EGraph = EGraph(SeqMap.empty, SeqMap.empty, SeqMap.empty)

  // TODO remove if not used
  type ClassRetriever = EClassId => EClass

}
