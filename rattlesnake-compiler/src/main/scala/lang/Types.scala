package lang

import identifiers.TypeIdentifier
import lang.Values.{And, Formula, IdValue}

import java.util.Objects


object Types {

  private val itForHashAndEquals = IdValue("it")

  sealed trait Type {
    def baseType: BaseType

    def itValueAndRefinementOpt: Option[(IdValue, Formula)]
  }

  final case class RefinedType(baseType: BaseType, itValue: IdValue, predicate: Formula) extends Type {

    override def itValueAndRefinementOpt: Option[(IdValue, Formula)] = Some(itValue -> predicate)

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

  sealed trait BaseType extends Type {
    def typeArgs: List[Type]

    override def baseType: BaseType = this
  }

  enum PrimitiveType(val str: String) extends BaseType {
    case IntType extends PrimitiveType("Int")
    case DoubleType extends PrimitiveType("Double")
    case CharType extends PrimitiveType("Char")
    case BoolType extends PrimitiveType("Bool")
    case StringType extends PrimitiveType("String")

    case NullType extends PrimitiveType("Null")
    case AnyType extends PrimitiveType("Any")
    case VoidType extends PrimitiveType("Void")
    case NothingType extends PrimitiveType("Nothing")

    override def itValueAndRefinementOpt: Option[(IdValue, Formula)] = None

    override def typeArgs: List[Type] = List.empty

    override def toString: String = str
  }

  def primTypeFor(name: TypeIdentifier): Option[PrimitiveType] = {
    PrimitiveType.values.find(_.str == name.stringId)
  }

  final case class NamedType(typeName: TypeIdentifier, typeArgs: List[Type], args: List[Formula]) extends BaseType {

    override def itValueAndRefinementOpt: Option[(IdValue, Formula)] = None

    def isSimpleName: Boolean = typeArgs.isEmpty && args.isEmpty

    override def toString: String = {
      val typeParamsDescr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      val paramsDescr = if args.isEmpty then "" else args.mkString("(", ",", ")")
      typeName.toString + typeParamsDescr + paramsDescr
    }
  }

  final class TypeVariable extends BaseType {
    private var actualTypeOpt = Option.empty[Type]

    def tryToResolve(tpe: Type): Unit = {
      val actualTpe = goUpPath(tpe)
      if (actualTpe != this) {
        actualTypeOpt = Some(actualTpe)
      }
    }

    def actualTypeIfKnown: Option[Type] = actualTypeOpt.map(goUpPath)

    def substitutedIfResolved: Type = actualTypeIfKnown.getOrElse(this)

    override def typeArgs: List[Type] = List.empty

    override def itValueAndRefinementOpt: Option[(IdValue, Formula)] = None

    override def toString: String = s"?${System.identityHashCode(this)}?"

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
          case baseTypeSubst: BaseType =>
            RefinedType(baseTypeSubst, itValueRaw, predicateRaw)
        }
      case primitiveType: PrimitiveType => primitiveType
      case NamedType(typeName, Nil, Nil) if typesSubst.contains(typeName) =>
        typesSubst.apply(typeName)
      case NamedType(typeName, typeArgs, args) =>
        NamedType(typeName, typeArgs.map(_.substitute(typesSubst, valsSubst)), args.map(_.substitute(typesSubst, valsSubst)))
      case tVar: TypeVariable => tVar
    }
  }
  
  def join(types: Type*): Type = join(types.toSet)
  
  def join(types: Set[Type]): Type = {
    ??? // TODO
  }

}
