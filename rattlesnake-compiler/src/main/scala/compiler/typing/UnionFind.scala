package compiler.typing

import compiler.lang.Formulas
import compiler.lang.Formulas.*
import compiler.lang.Types.{IntersectionType, Type}

import scala.annotation.tailrec
import scala.collection.mutable


trait UnionFind {

  def representativeOf(value: IdValue): IdValue

  def knows(idValue: IdValue): Boolean

  def rawReprOf(idValue: IntermediateIdValue): Option[Formula]

  def canonicReprOf(idValue: IntermediateIdValue): Option[Formula] =
    rawReprOf(idValue).map(canonicalize)

  def filterFormula(f: Formula): Option[Formula] = f match {
    case value: IdValue => Option.when(knows(value))(canonicalize(value))
    case formula: ConstFormula => Some(formula)
    case Select(owner, field) => for ow <- filterFormula(owner) yield Select(ow, field)
    case Call(receiver, func, args) =>
      val filteredRecOpt = filterFormula(receiver)
      val filteredArgs = args.flatMap(filterFormula)
      for filteredReceiverOpt <- filteredRecOpt
          if filteredArgs.size == args.size yield Call(filteredReceiverOpt, func, filteredArgs)
    case Plus(lhs, rhs) =>
      for {
        flhs <- filterFormula(lhs)
        frhs <- filterFormula(rhs)
      } yield Plus(flhs, frhs)
    case Neg(operand) =>
      for filteredOperand <- filterFormula(operand) yield Neg(filteredOperand)
    case Times(lhs, rhs) =>
      for {
        flhs <- filterFormula(lhs)
        frhs <- filterFormula(rhs)
      } yield Times(flhs, frhs)
    case DivBy(lhs, rhs) =>
      for {
        flhs <- filterFormula(lhs)
        frhs <- filterFormula(rhs)
      } yield DivBy(flhs, frhs)
    case Modulo(lhs, rhs) =>
      for {
        flhs <- filterFormula(lhs)
        frhs <- filterFormula(rhs)
      } yield Modulo(flhs, frhs)
  }

  def canonicalize(formula: Formula): Formula = formula match {
    case value: IdValue => representativeOf(value)
    case cst: Formulas.ConstFormula => cst
    case Select(owner, field) =>
      Select(canonicalize(owner), field)
    case Call(receiver, func, args) =>
      Call(canonicalize(receiver), func, args.map(canonicalize))
    case Plus(lhs, rhs) =>
      Plus(canonicalize(lhs), canonicalize(rhs))
    case Neg(operand) =>
      Neg(canonicalize(operand))
    case Times(lhs, rhs) =>
      Times(canonicalize(lhs), canonicalize(rhs))
    case DivBy(lhs, rhs) =>
      DivBy(canonicalize(lhs), canonicalize(rhs))
    case Modulo(lhs, rhs) =>
      Modulo(canonicalize(lhs), canonicalize(rhs))
  }

}


final class MutableUnionFind extends UnionFind {
  private val representatives: mutable.Map[IdValue, IdValue] = mutable.Map.empty
  private val valsDefs: mutable.Map[IntermediateIdValue, Formula] = mutable.Map.empty
  private val types: mutable.Map[IdValue, Type] = mutable.Map.empty
  private var smartcasts: mutable.Map[Formula, Type] = mutable.Map.empty

  override def knows(idValue: IdValue): Boolean = representatives.contains(idValue)

  def representativeOf(idVal: IdValue): IdValue = {
    representatives.get(idVal) match {
      case Some(nextIdVal) =>
        val repr = representativeOf(nextIdVal)
        representatives(idVal) = repr
        repr
      case None => idVal
    }
  }

  override def rawReprOf(idValue: IntermediateIdValue): Option[Formula] = valsDefs.get(idValue)

  def mkEqual(a: IdValue, b: IdValue): Unit = {
    val ra = representativeOf(a)
    val rb = representativeOf(b)
    if (ra == rb) {
      return
    }
    if (ra.definingScope.depth < rb.definingScope.depth || ra.definingScope.depth == rb.definingScope.depth && ra.uid < rb.uid) {
      representatives(rb) = ra
      types.get(rb).foreach { tb =>
        types.updateWith(ra) {
          case Some(oldType) if oldType != tb => Some(IntersectionType(oldType, tb))
          case None => Some(tb)
        }
      }
    } else {
      representatives(ra) = rb
    }
    smartcasts = for (f, tpe) <- smartcasts yield canonicalize(f) -> tpe
  }

  def saveType(idVal: IdValue, tpe: Type): Unit = {
    types(representativeOf(idVal)) = tpe
  }

  def saveSmartcast(formula: Formula, tpe: Type): Unit = {
    smartcasts(canonicalize(formula)) = tpe
  }

  def saveValDef(idValue: IntermediateIdValue, df: Formula): Unit = {
    valsDefs(idValue) = df
  }

  def deepCopy: MutableUnionFind = {
    val copy = MutableUnionFind()
    copy.representatives.addAll(this.representatives)
    copy.types.addAll(this.types)
    copy
  }

  def snapshot: ImmutableUnionFind =
    ImmutableUnionFind(representatives.toMap, valsDefs.toMap, types.toMap, smartcasts.toMap)

  def clear(): Unit = {
    representatives.clear()
    types.clear()
  }

}

final case class ImmutableUnionFind(
                                     representatives: Map[IdValue, IdValue],
                                     valsDefs: Map[IntermediateIdValue, Formula],
                                     types: Map[IdValue, Type],
                                     smartcasts: Map[Formula, Type]
                                   ) extends UnionFind {

  override def knows(idValue: IdValue): Boolean = representatives.contains(idValue)

  override def representativeOf(value: IdValue): IdValue =
    representatives.getOrElse(value, value)

  override def rawReprOf(idValue: IntermediateIdValue): Option[Formula] =
    valsDefs.get(idValue)
}
