package lang

import identifiers.TypeIdentifier
import lang.Values.{And, Formula, IdValue}

import java.util.Objects


object Types {

  sealed trait Type {
    def baseType: BaseType
  }

  final case class RefinedType(baseType: BaseType, itValue: IdValue, predicate: Formula) extends Type {

    override def equals(other: Any): Boolean = other match {
      case RefinedType(otherBaseType, otherItValue, otherPredicate) =>
        baseType == otherBaseType && (
          (itValue == otherItValue && predicate == otherPredicate) ||
            predicate == otherPredicate.substitute(Map.empty, Map(otherItValue -> itValue)))
      case _ => false
    }

    override def hashCode(): Int = Objects.hash(baseType, predicate.substitute(Map.empty, Map(itValue -> IdValue("it"))))

    override def toString: String = s"$baseType $itValue with $predicate"
  }

  sealed trait BaseType extends Type {
    def typeArgs: List[Type]

    override def baseType: BaseType = this
  }

  trait TypeVar extends BaseType

  enum PrimitiveType(val str: String) extends BaseType {
    case IntType extends PrimitiveType("Int")
    case DoubleType extends PrimitiveType("Double")
    case CharType extends PrimitiveType("Char")
    case BoolType extends PrimitiveType("Bool")
    case StringType extends PrimitiveType("String")
    case NullType extends PrimitiveType("Null")

    case VoidType extends PrimitiveType("Void")
    case NothingType extends PrimitiveType("Nothing")

    override def typeArgs: List[Type] = List.empty

    override def toString: String = str
  }

  def primTypeFor(name: TypeIdentifier): Option[PrimitiveType] = {
    PrimitiveType.values.find(_.str == name.stringId)
  }

  final case class NamedType(typeName: TypeIdentifier, typeArgs: List[Type], args: List[Formula]) extends BaseType {
    override def toString: String = {
      val typeParamsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      val paramsDescr = if args.isEmpty then "" else args.mkString("(", ",", ")")
      typeName.toString + typeParamsDescr + paramsDescr
    }
  }

  extension (tpe: Type) {

    def substituteVar(targetVar: TypeVar, replacement: Type): Type = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        baseTypeRaw.substituteVar(targetVar, replacement) match {
          case RefinedType(baseTypeSubst, itValueSubst, predicateSubst) =>
            RefinedType(baseTypeSubst, itValueRaw, And(predicateRaw, predicateSubst.substitute(Map.empty, Map(itValueSubst -> itValueRaw))))
          case baseTypeSubst: BaseType => RefinedType(baseTypeSubst, itValueRaw, predicateRaw)
        }
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, typeParams, params) =>
        NamedType(typeName, typeParams.map(_.substituteVar(targetVar, replacement)), params)
      case typeVar: TypeVar if typeVar == targetVar => replacement
      case typeVar: TypeVar => typeVar
    }

    def substitute(typesSubst: Map[TypeIdentifier, Type], valsSubst: Map[IdValue, Formula]): Type = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        baseTypeRaw.substitute(typesSubst, valsSubst) match {
          case RefinedType(baseTypeSubst, itValueSubst, predicateSubst) =>
            RefinedType(baseTypeRaw, itValueRaw, And(predicateRaw, predicateSubst.substitute(typesSubst, valsSubst ++ Map(itValueSubst -> itValueRaw))))
          case baseTypeSubst: BaseType =>
            RefinedType(baseTypeSubst, itValueRaw, predicateRaw)
        }
      case typeVar: TypeVar => typeVar
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, Nil, Nil) if typesSubst.contains(typeName) =>
        typesSubst.apply(typeName)
      case NamedType(typeName, typeArgs, args) =>
        NamedType(typeName, typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(typesSubst, valsSubst)))
    }
  }

}
