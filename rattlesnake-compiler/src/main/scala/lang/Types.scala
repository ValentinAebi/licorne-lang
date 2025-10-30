package lang

import identifiers.TypeIdentifier
import lang.CaptureDescriptors.*
import lang.Values.Formula


object Types {

  final case class Type(shape: TypeShape, cs: CaptureSet, refinementOpt: Option[Formula]) {
    override def toString: String = {
      val csDescr = if cs.isEmpty then "" else s"^${cs.toString}"
      val refinementDescr = refinementOpt.map(r => s" with $r").getOrElse("")
      shape.toString + csDescr + refinementDescr
    }
  }

  sealed trait TypeShape {
    def typeParams: List[Type]
    def toType: Type = Type(this, CaptureSet.empty, None)
  }

  enum PrimitiveTypeShape(val str: String) extends TypeShape {
    case IntType extends PrimitiveTypeShape("Int")
    case DoubleType extends PrimitiveTypeShape("Double")
    case CharType extends PrimitiveTypeShape("Char")
    case BoolType extends PrimitiveTypeShape("Bool")
    case StringType extends PrimitiveTypeShape("String")

    case VoidType extends PrimitiveTypeShape("Void")
    case NothingType extends PrimitiveTypeShape("Nothing")

    override def typeParams: List[Type] = List.empty

    override def toString: String = str
  }

  def primTypeFor(name: TypeIdentifier): Option[PrimitiveTypeShape] = {
    PrimitiveTypeShape.values.find(_.str == name.stringId)
  }

  final case class NamedTypeShape(typeName: TypeIdentifier, typeParams: List[Type], params: List[Formula]) extends TypeShape {
    override def toString: String = {
      val typeParamsDescr = if typeParams.isEmpty then "" else typeParams.mkString("<", ",", ">")
      val paramsDescr = if params.isEmpty then "" else params.mkString("(", ",", ")")
      typeName.toString + typeParamsDescr + paramsDescr
    }
  }

  /**
   * Type of a malformed/incorrect expression
   */
  case object UndefinedTypeShape extends TypeShape {
    override def typeParams: List[Type] = List.empty
    override def toString: String = "[undefined type]"
  }

}
