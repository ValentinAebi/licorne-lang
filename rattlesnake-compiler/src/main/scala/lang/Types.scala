package lang

import identifiers.{ItId, TypeIdentifier}
import lang.Types.PrimitiveType.NothingType
import lang.Values.{And, Formula, IdValue}

import java.util.Objects
import java.util.concurrent.atomic.AtomicLong


object Types {

  private val itForHashAndEquals = IdValue("it$hash", 1)

  sealed trait Type {
    def baseType: BaseType
  }

  final case class RefinedType private(baseType: NominalType, itValue: IdValue, predicate: Formula) extends Type {

    override def equals(other: Any): Boolean = other match {
      case RefinedType(otherBaseType, otherItValue, otherPredicate) =>
        baseType == otherBaseType && (
          (itValue == otherItValue && predicate == otherPredicate) ||
            predicate == otherPredicate.substitute(Map.empty, Map(otherItValue -> itValue)))
      case _ => false
    }

    override def hashCode(): Int = Objects.hash(baseType, predicate.substitute(Map.empty, Map(itValue -> itForHashAndEquals)))

    override def toString: String = s"$baseType $itValue with $predicate"
  }

  object RefinedType {
    def apply(baseType: NominalType, itValue: IdValue, predicate: Formula): Type =
      baseType match {
        case NothingType => NothingType
        case _ => new RefinedType(baseType, itValue, predicate)
      }
  }

  final case class UnionType(types: Set[Type]) extends Type {
    override def baseType: BaseType = BaseUnionType(types.map(_.baseType))

    override def toString: String = types.mkString(" | ")
  }

  final case class BaseUnionType(types: Set[BaseType]) extends BaseType {
    override def toString: String = types.mkString(" | ")
  }

  sealed trait BaseType extends Type {
    override def baseType: BaseType = this
  }
  
  sealed trait NominalType extends BaseType

  enum PrimitiveType(val str: String) extends NominalType {
    case IntType extends PrimitiveType("Int")
    case DoubleType extends PrimitiveType("Double")
    case CharType extends PrimitiveType("Char")
    case BoolType extends PrimitiveType("Bool")
    case StringType extends PrimitiveType("String")

    case NullType extends PrimitiveType("Null")
    case AnyType extends PrimitiveType("Any")
    case VoidType extends PrimitiveType("Void")
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

  private val typeVarUidGen = new AtomicLong()

  final class TypeVariable(descr: String) extends BaseType {
    private val uid = typeVarUidGen.incrementAndGet()
    private var actualTypeOpt = Option.empty[Type]

    def tryToResolve(tpe: Type): Unit = {
      val actualTpe = goUpPath(tpe)
      if (actualTpe != this) {
        actualTypeOpt = Some(actualTpe)
      }
    }

    def actualTypeIfKnown: Option[Type] = actualTypeOpt.map(goUpPath)

    def substitutedIfResolved: Type = actualTypeIfKnown.getOrElse(this)

    override def toString: String = s"?${descr}_$uid"

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

  extension (tpe: Type) {

    def substitute(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Type = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        baseTypeRaw.substitute(typesSubst, valsSubst) match {
          case RefinedType(baseTypeSubst, itValueSubst, predicateSubst) =>
            RefinedType(baseTypeRaw, itValueRaw, And(predicateRaw, predicateSubst.substitute(typesSubst, valsSubst ++ Map(itValueSubst -> itValueRaw))))
          case baseTypeSubst: NominalType =>
            RefinedType(baseTypeSubst, itValueRaw, predicateRaw)
          case _: (UnionType | BaseUnionType | TypeVariable) => throw new AssertionError("")
        }
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, Nil, Nil) if typesSubst.contains(typeName) =>
        typesSubst.apply(typeName)
      case NamedType(typeName, typeArgs, args) =>
        NamedType(typeName, typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(typesSubst, valsSubst)))
      case tVar: TypeVariable => tVar
      case UnionType(types) => UnionType(types.map(_.substitute(typesSubst, valsSubst)))
      case BaseUnionType(originalBaseTypes) =>
        val substTypes = originalBaseTypes.map(_.substitute(typesSubst, valsSubst))
        if substTypes.forall(_.isInstanceOf[BaseType])
        then BaseUnionType(substTypes.map(_.asInstanceOf[BaseType]))
        else UnionType(substTypes)
    }

    def withTypeVarsExpanded: Type = tpe match {
      case RefinedType(baseType, itValue, predicate) =>
        baseType.withTypeVarsExpanded.baseType match {
          case nominalType: NominalType => RefinedType(nominalType, itValue, predicate)
          case otherType => otherType
        }
      case UnionType(types) => UnionType(types.map(_.withTypeVarsExpanded))
      case BaseUnionType(types) =>
        BaseUnionType(types.map(_.withTypeVarsExpanded.baseType))
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, typeArgs, args) => NamedType(typeName, typeArgs.map(_.withTypeVarsExpanded), args)
      case variable: TypeVariable => variable.substitutedIfResolved
    }

  }

  def join(types: Type*): Type = join(types.toSet)

  def join(typesRaw: Set[Type]): Type = {
    val nonNothingTypes = typesRaw.filterNot(_.baseType == NothingType)
    nonNothingTypes.size match {
      case 0 => NothingType
      case 1 => nonNothingTypes.head
      case _ => UnionType(nonNothingTypes)
    }
  }

}
