package compiler.typing

import compiler.lang.Formulas.*
import compiler.lang.Types.*
import compiler.lang.{Formulas, Types}
import compiler.smt.Simplifier

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
    case cst: ConstFormula => cst
    case Select(owner, field) =>
      Select(canonicalize(owner), field)
    case Call(receiver, func, typeArgs, args) =>
      Call(canonicalize(receiver), func, typeArgs.map(canonicalize), args.map(canonicalize))
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
    case LogicalAnd(lhs, rhs) =>
      LogicalAnd(canonicalize(lhs), canonicalize(rhs))
    case LogicalOr(lhs, rhs) =>
      LogicalOr(canonicalize(lhs), canonicalize(rhs))
    case LogicalNot(operand) =>
      LogicalNot(canonicalize(operand))
    case Equality(lhs, rhs) =>
      Equality(canonicalize(lhs), canonicalize(rhs))
    case LessOrEq(lhs, rhs) =>
      LessOrEq(canonicalize(lhs), canonicalize(rhs))
    case LessThan(lhs, rhs) =>
      LessThan(canonicalize(lhs), canonicalize(rhs))
    case TypePredicate(subject, tpe) =>
      TypePredicate(canonicalize(subject), tpe)
  }
  
  private def canonicalize(tpe: Type): Type = tpe match {
    case primitiveType: PrimitiveType => primitiveType
    case NamedType(typeName, typeArgs, args) =>
      NamedType(typeName, typeArgs.map(canonicalize), args.map(canonicalize))
    case ClosureType(params, result) =>
      ClosureType(params.map(canonicalize), canonicalize(result))
    case tv: TypeVariable => tv
    case UnionType(types) =>
      UnionType(types.map(canonicalize))
    case IntersectionType(types) =>
      IntersectionType(types.map(canonicalize))
    case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
      IntRangeType(lowerBoundOpt.map(canonicalize), upperBoundOpt.map(canonicalize))
  }

}


final class MutableUnionFind extends UnionFind {
  private val representatives: mutable.Map[IdValue, IdValue] = mutable.Map.empty
  private val types: mutable.Map[IdValue, Type] = mutable.Map.empty
  private var smartcasts: mutable.Map[Formula, Type] = mutable.Map.empty
  
  def copy: MutableUnionFind = {
    val copy = MutableUnionFind()
    copy.representatives.addAll(this.representatives)
    copy.types.addAll(this.types)
    copy.smartcasts.addAll(this.types)
    copy
  }

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

  def saveSmartcast(formula: Formula, tpe: Type)(using simplifier: Simplifier): Unit = {
    val canonicFormula = canonicalize(formula)
    smartcasts(canonicFormula) = smartcasts.get(canonicFormula) match {
      case Some(IntersectionType(types)) =>
        simplifier.simplify(IntersectionType(types.incl(tpe)))
      case Some(prevType) =>
        simplifier.simplify(IntersectionType(prevType, tpe))
      case None => tpe
    }
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
