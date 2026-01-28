package lang

import identifiers.TypeIdentifier
import lang.Formulas.*
import lang.Types.PrimitiveType.{AnyType, IntType, NothingType}
import lang.Types.IntRangeType.Bound
import lang.Types.IntRangeType.Bound.*

import java.util.Objects
import java.util.concurrent.atomic.AtomicLong


object Types {

  private val itForHashAndEquals = new IdValue {
    override def completeDescr: String = "it$hash"

    override def sourceLevelDescrOrDefault: String = "it"
  }

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

    case NullType extends PrimitiveType("Null")
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
  
  final case class UnionType(types: Set[Type]) extends RefinedType {
    override def principalType: PrincipalType = if types.size == 1 then types.head.principalType else AnyType

    override def toString: String = types.mkString(" | ")
  }
  
  final case class IntersectionType(types: Set[Type]) extends RefinedType {
    override def principalType: PrincipalType = AnyType

    override def toString: String = types.mkString(" & ")
  }

  final case class IntRangeType(lowerBound: Bound, upperBound: Bound) extends RefinedType {
    override def principalType: PrincipalType = IntType

    override def toString: String = s"[$lowerBound,$upperBound]"
  }

  object IntRangeType {

    def apply(low: Formula, up: Formula): IntRangeType =
      new IntRangeType(Max(Set(low)), Min(Set(up)))

    enum Bound {
      case Simple(bound: Formula)
      case Max(bounds: Set[Formula])
      case Min(bounds: Set[Formula])
      case NoBound

      def collectFormulas[T](action: Formula => T): Set[T] = this match {
        case Bound.Simple(bound) => Set(action(bound))
        case Bound.Max(bounds) => bounds.map(action)
        case Bound.Min(bounds) => bounds.map(action)
        case Bound.NoBound => Set.empty
      }

      override def toString: String = this match {
        case Bound.Simple(bound) => bound.toString
        case Bound.Max(bounds) => bounds.mkString("max{", ",", "}")
        case Bound.Min(bounds) => bounds.mkString("min{", ",", "}")
        case Bound.NoBound => ""
      }

    }
  }

  private val typeVarUidGen = new AtomicLong()

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
        NamedType(typeName, typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(typesSubst, valsSubst)))
      case tVar: TypeVariable => tVar
      case ClosureType(params, result) =>
        ClosureType(params.map(_.substitute(typesSubst, valsSubst)), result.substitute(typesSubst, valsSubst))
      case UnionType(types) =>
        UnionType(types.map(_.substitute(typesSubst, valsSubst)))
      case IntersectionType(types) =>
        IntersectionType(types.map(_.substitute(typesSubst, valsSubst)))
      case IntRangeType(lowerBound, upperBound) =>
        IntRangeType(lowerBound.substitute(typesSubst, valsSubst), upperBound.substitute(typesSubst, valsSubst))
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

  extension (bound: Bound) private def substitute(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Bound = bound match {
    case Bound.Simple(bound) => Bound.Simple(bound.substitute(typesSubst, valsSubst))
    case Bound.Max(bounds) => Bound.Max(bounds.map(_.substitute(typesSubst, valsSubst)))
    case Bound.Min(bounds) => Bound.Min(bounds.map(_.substitute(typesSubst, valsSubst)))
    case Bound.NoBound => Bound.NoBound
  }

  def join(types: Type*): Type = join(types.toSet)

  def join(typesRaw: Set[Type]): Type = {
    val nonNothingTypes = typesRaw - NothingType
    nonNothingTypes.size match {
      case 0 => NothingType
      case 1 => nonNothingTypes.head
      case _ => UnionType(nonNothingTypes)
    }
  }

}
