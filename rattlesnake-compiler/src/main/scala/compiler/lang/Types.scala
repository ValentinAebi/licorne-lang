package compiler.lang

import Formulas.*
import Types.PrimitiveType.{AnyType, IntType, NothingType}
import compiler.identifiers.TypeIdentifier
import compiler.util.SeqSet

import java.util.concurrent.atomic.AtomicLong
import scala.collection.SeqMap


object Types {

  sealed trait Type {
    def principalType: PrincipalType
  }

  sealed trait PrincipalType extends Type {
    override final def principalType: PrincipalType = this
  }

  sealed trait RefinedType extends Type

  sealed trait NominalType extends PrincipalType

  enum PrimitiveType(val str: String) extends NominalType {
    case IntType extends PrimitiveType("Int")
    case DoubleType extends PrimitiveType("Double")
    case CharType extends PrimitiveType("Char")
    case BoolType extends PrimitiveType("Bool")
    case StringType extends PrimitiveType("String")

    case NullType extends PrimitiveType("Null") // FIXME handle this one (and implement nullable types)
    case AnyType extends PrimitiveType("Any")
    case UnitType extends PrimitiveType("Unit")
    case NothingType extends PrimitiveType("Nothing")

    override def toString: String = str
  }

  def primTypeFor(name: TypeIdentifier): Option[PrimitiveType] = {
    PrimitiveType.values.find(_.str == name.stringId)
  }

  final case class NamedType(typeName: TypeIdentifier, typeArgs: List[Type], args: List[Formula]) extends NominalType {

    def isSimpleName: Boolean = typeArgs.isEmpty && args.isEmpty

    override def toString: String = {
      val typeParamsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      val paramsDescr = if args.isEmpty then "" else args.mkString("(", ",", ")")
      typeName.toString + typeParamsDescr + paramsDescr
    }
  }

  final case class ClosureType(params: List[Type], result: Type) extends PrincipalType {
    override def toString: String = s"(${params.mkString(", ")}) -> $result"
  }

  final case class UnionType(types: SeqSet[Type]) extends RefinedType {
    override def principalType: PrincipalType = if types.size == 1 then types.head.principalType else AnyType

    override def toString: String = types.mkString(" | ")
  }

  object UnionType {
    def apply(types: Type*): UnionType =
      UnionType(SeqSet(types))
  }

  final case class IntersectionType(types: SeqSet[Type]) extends RefinedType {
    override def principalType: PrincipalType = AnyType

    override def toString: String = types.mkString(" & ")
  }

  object IntersectionType {
    def apply(types: Type*): IntersectionType = {
      val typesB = SeqSet.newBuilder[Type]
      types.foreach {
        case IntersectionType(nestedTypes) => typesB.addAll(nestedTypes)
        case tpe => typesB.addOne(tpe)
      }
      IntersectionType(typesB.build())
    }
  }

  final case class IntRangeType(lowerBoundOpt: Option[Formula], upperBoundOpt: Option[Formula]) extends RefinedType {
    override def principalType: PrincipalType = IntType

    override def toString: String = {
      def boundDescr(bound: Option[Formula]): String = bound.map(_.toString).getOrElse("")

      s"[${boundDescr(lowerBoundOpt)},${boundDescr(upperBoundOpt)}]"
    }
  }

  object IntRangeType {

    def singleton(elem: Formula): IntRangeType =
      IntRangeType(Some(elem), Some(elem))

    def ofLowerBound(lb: Formula): IntRangeType =
      IntRangeType(Some(lb), None)

    def ofUpperBound(ub: Formula): IntRangeType =
      IntRangeType(None, Some(ub))

  }

  private val typeVarUidGen = new AtomicLong(-1)

  final class TypeVariable private(name: String, val upperBoundOpt: Option[Type], val lowerBoundOpt: Option[Type]) extends PrincipalType {
    private val uid = typeVarUidGen.incrementAndGet()
    private var actualTypeOpt = Option.empty[Type]

    def resolve(tpe: Type): Unit = {
      if (isResolved) {
        throw IllegalStateException("type variable was already resolved")
      }
      val actualTpe = goUpPath(tpe)
      if (actualTpe != this) {
        actualTypeOpt = Some(actualTpe)
      }
    }

    def actualTypeIfResolved: Option[Type] = actualTypeOpt.map(goUpPath)

    def isResolved: Boolean = actualTypeIfResolved.isDefined

    def substitutedIfResolved: Type = actualTypeIfResolved.getOrElse(this)

    override def toString: String = name

    private def goUpPath(tpe: Type): Type = tpe match {
      case tVar: TypeVariable => tVar.actualTypeOpt match {
        case Some(actualType) =>
          val repr = goUpPath(actualType)
          tVar.actualTypeOpt = Some(repr)
          repr
        case None => tpe
      }
      case _ => tpe
    }
  }

  object TypeVariable {
    def apply(name: String, upperBoundOpt: Option[Type], lowerBoundOpt: Option[Type])(tvRegistrator: TypeVariable => Unit): TypeVariable = {
      val tv = new TypeVariable(name, upperBoundOpt, lowerBoundOpt)
      tvRegistrator(tv)
      tv
    }
  }

  extension (tpe: Type) {

    def substitute(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Type = tpe match {
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, Nil, Nil) if typesSubst.contains(typeName) =>
        typesSubst.apply(typeName)
      case NamedType(typeName, typeArgs, args) =>
        NamedType(typeName, typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(valsSubst)))
      case tVar: TypeVariable => tVar
      case ClosureType(params, result) =>
        ClosureType(params.map(_.substitute(typesSubst, valsSubst)), result.substitute(typesSubst, valsSubst))
      case UnionType(types) =>
        UnionType(types.map(_.substitute(typesSubst, valsSubst)))
      case IntersectionType(types) =>
        IntersectionType(types.map(_.substitute(typesSubst, valsSubst)))
      case IntRangeType(lowerBoundOpt, upperBoundOpt) =>
        IntRangeType(
          lowerBoundOpt.map(_.substitute(valsSubst)),
          upperBoundOpt.map(_.substitute(valsSubst))
        )
    }

    def withTypeVarsExpanded: Type = tpe match {
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, typeArgs, args) => NamedType(typeName, typeArgs.map(_.withTypeVarsExpanded), args)
      case ClosureType(params, result) => ClosureType(params.map(_.withTypeVarsExpanded), result.withTypeVarsExpanded)
      case variable: TypeVariable => variable.substitutedIfResolved
      case UnionType(types) =>
        UnionType(types.map(_.withTypeVarsExpanded))
      case IntersectionType(types) =>
        IntersectionType(types.map(_.withTypeVarsExpanded))
      case range: IntRangeType => range
    }

  }

}
