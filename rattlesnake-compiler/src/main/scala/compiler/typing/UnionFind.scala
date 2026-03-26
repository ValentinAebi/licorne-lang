package compiler.typing

import compiler.lang.Formulas
import compiler.lang.Formulas.*
import compiler.lang.Types.{IntersectionType, Type}
import compiler.simplification.Simplifier

import scala.annotation.tailrec
import scala.collection.mutable


trait UnionFind {

  def representativeOf(value: IdValue): IdValue

  def typeOfNoSmartcast(value: IdValue): Option[Type]

  def typeOfNoSmartcast(formula: Formula): Option[Type] = formula match {
    case idValue: IdValue => typeOfNoSmartcast(idValue)
    case _ => None
  }

  def smartcastTypeOf(f: Formula): Option[Type]

  def currentTypeOf(formula: Formula): Option[Type] =
    smartcastTypeOf(formula)
      .orElse(typeOfNoSmartcast(formula))

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
    // FIXME additional cases
  }

}


final class MutableUnionFind(simplifier: Simplifier) extends UnionFind {
  private val representatives: mutable.Map[IdValue, IdValue] = mutable.Map.empty
  private val types: mutable.Map[IdValue, Type] = mutable.Map.empty
  private var smartcasts: mutable.Map[Formula, Type] = mutable.Map.empty

  def representativeOf(idVal: IdValue): IdValue = {
    representatives.get(idVal) match {
      case Some(nextIdVal) =>
        val repr = representativeOf(nextIdVal)
        representatives(idVal) = repr
        repr
      case None => idVal
    }
  }

  override def typeOfNoSmartcast(value: IdValue): Option[Type] = types.get(value)

  override def smartcastTypeOf(f: Formula): Option[Type] = smartcasts.get(f)

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
          case _ => Some(tb)
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
    val canonicFormula = canonicalize(formula)
    smartcasts(canonicFormula) = smartcasts.get(canonicFormula) match {
      case Some(IntersectionType(types)) =>
        simplifier.simplify(IntersectionType(types.incl(tpe)))
      case Some(prevType) =>
        simplifier.simplify(IntersectionType(prevType, tpe))
      case None => tpe
    }
  }

  def deepCopy: MutableUnionFind = {
    val copy = MutableUnionFind(simplifier)
    copy.representatives.addAll(this.representatives)
    copy.types.addAll(this.types)
    copy
  }

  def snapshot: ImmutableUnionFind =
    ImmutableUnionFind(representatives.toMap, types.toMap, smartcasts.toMap)

  def clear(): Unit = {
    representatives.clear()
    types.clear()
  }

}

final case class ImmutableUnionFind(
                                     representatives: Map[IdValue, IdValue],
                                     types: Map[IdValue, Type],
                                     smartcasts: Map[Formula, Type]
                                   ) extends UnionFind {

  override def representativeOf(value: IdValue): IdValue =
    representatives.getOrElse(value, value)

  override def typeOfNoSmartcast(value: IdValue): Option[Type] = types.get(value)

  override def smartcastTypeOf(f: Formula): Option[Type] = smartcasts.get(f)

}
