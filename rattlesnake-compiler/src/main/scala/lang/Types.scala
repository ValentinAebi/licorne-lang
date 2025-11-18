package lang

import identifiers.TypeIdentifier
import lang.Values.{Formula, IdValue}


object Types {

  sealed trait Type {
    def withoutRefinement: BasicType
  }

  final case class RefinedType(baseType: Type, itValue: IdValue, predicate: Formula) extends Type {
    override def withoutRefinement: BasicType = baseType.withoutRefinement
    override def toString: String = s"$baseType with $predicate"
  }

  sealed trait BasicType extends Type {
    def typeParams: List[Type]
    override def withoutRefinement: BasicType = this
  }

  enum PrimitiveType(val str: String) extends BasicType {
    case IntType extends PrimitiveType("Int")
    case DoubleType extends PrimitiveType("Double")
    case CharType extends PrimitiveType("Char")
    case BoolType extends PrimitiveType("Bool")
    case StringType extends PrimitiveType("String")

    case VoidType extends PrimitiveType("Void")
    case NothingType extends PrimitiveType("Nothing")

    override def typeParams: List[Type] = List.empty

    override def toString: String = str
  }

  def primTypeFor(name: TypeIdentifier): Option[PrimitiveType] = {
    PrimitiveType.values.find(_.str == name.stringId)
  }

  final case class NamedType(typeName: TypeIdentifier, typeParams: List[Type], params: List[Formula], isPure: Boolean)
    extends BasicType {
    override def toString: String = {
      val typeParamsDescr = if typeParams.isEmpty then "" else typeParams.mkString("<", ",", ">")
      val paramsDescr = if params.isEmpty then "" else params.mkString("(", ",", ")")
      val purityDescr = if isPure then "" else "'"
      typeName.toString + typeParamsDescr + paramsDescr + purityDescr
    }
  }

  /**
   * Type of a malformed/incorrect expression
   */
  case object UndefinedType extends BasicType {
    override def typeParams: List[Type] = List.empty

    override def toString: String = "[undefined type]"
  }

}
