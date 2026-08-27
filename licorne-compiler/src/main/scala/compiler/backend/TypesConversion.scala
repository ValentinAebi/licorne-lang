package compiler.backend

import compiler.backend.Boxing.boxDesc
import compiler.identifiers.TypeIdentifier
import compiler.lang.Types
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.stdlib.StdLib
import compiler.typing.contexts.{DealiasingContext, TypeParamsContext}
import compiler.backend.Erasure.getRuntimeType

import java.lang.classfile.TypeKind
import java.lang.classfile.TypeKind.*
import java.lang.constant.ClassDesc
import java.lang.constant.ConstantDescs.*

trait TypesConverter {

  protected val dealiasingCtx: DealiasingContext

  protected val intDesc: ClassDesc
  protected val doubleDesc: ClassDesc
  protected val charDesc: ClassDesc
  protected val boolDesc: ClassDesc

  def descriptorFor(tpe: Type)(using tpCtx: TypeParamsContext): ClassDesc =
    getRuntimeType(tpe)(using tpCtx, dealiasingCtx) match {
      case tpe: PrimitiveType => descriptorForPrimitive(tpe)
      case NamedType(StdLib.arrayTypeId, List(elemType), Nil) =>
        descriptorFor(elemType).arrayType()
      case NamedType(typeName, typeArgs, args) => descriptorFor(typeName)
      case ClosureType(params, result, enforcedPure) => ???
      case UnionType(types) =>
        val descriptors = types.map(descriptorFor)
        if descriptors.size == 1 then descriptors.head
        else descriptorFor(AnyType)
      case IntersectionType(types) =>
        val descriptors = types.map(descriptorFor)
        descriptors.find(_.isPrimitive) match {
          case Some(primDesc) => primDesc
          case None => descriptors.head
        }
      case RefinedType(baseType, predicate) => descriptorFor(baseType)
      case IntRangeType(_, _) => CD_int
      case NullableType(nullatedType) => boxDesc(descriptorFor(nullatedType))
      case tv: TypeVariable => descriptorFor(tv.upperBoundOpt.getOrElse(NullableType(AnyType)))
    }

  def descriptorForPrimitive(tpe: PrimitiveType): ClassDesc = tpe match {
    case IntType => intDesc
    case DoubleType => doubleDesc
    case CharType => charDesc
    case BoolType => boolDesc
    case NullType => CD_Object
    case AnyType => CD_Object
    case UnitType => CD_void
    case NothingType => CD_void
  }

  def descriptorFor(typeName: TypeIdentifier): ClassDesc = {
    if typeName == StdLib.stringTypeId then CD_String
    else ClassDesc.of(typeName.stringId)
  }

  def kindFor(tpe: Type)(using tpCtx: TypeParamsContext): TypeKind = getRuntimeType(tpe)(using tpCtx, dealiasingCtx) match {
    case IntType => INT
    case DoubleType => DOUBLE
    case CharType => CHAR
    case BoolType => BOOLEAN
    case NullType => REFERENCE
    case AnyType => REFERENCE
    case UnitType => VOID
    case NothingType => VOID
    case UnionType(types) =>
      val kinds = types.map(kindFor)
      if kinds.size == 1 then kinds.head
      else REFERENCE
    case IntersectionType(types) =>
      types.find(_.isInstanceOf[PrimitiveType]) match {
        case Some(primType) => kindFor(primType)
        case None => kindFor(types.head)
      }
    case tpe: (NamedType | ClosureType) => REFERENCE
    case RefinedType(baseType, predicate) => kindFor(baseType)
    case IntRangeType(_, _) => INT
    case NullableType(_) => REFERENCE
    case tv: TypeVariable => kindFor(tv.upperBoundOpt.getOrElse(NullableType(AnyType)))
  }

}

final class BoxingTypesConverter(override protected val dealiasingCtx: DealiasingContext) extends TypesConverter {
  override protected val intDesc: ClassDesc = CD_Integer
  override protected val doubleDesc: ClassDesc = CD_Double
  override protected val charDesc: ClassDesc = CD_Character
  override protected val boolDesc: ClassDesc = CD_Boolean
}

object BoxingTypesConverter {
  def fromAmbientDealiasingCtx(using dealiasingCtx: DealiasingContext): BoxingTypesConverter =
    BoxingTypesConverter(dealiasingCtx)
}

final class NonBoxingTypesConverter(override protected val dealiasingCtx: DealiasingContext) extends TypesConverter {
  override protected val intDesc: ClassDesc = CD_int
  override protected val doubleDesc: ClassDesc = CD_double
  override protected val charDesc: ClassDesc = CD_char
  override protected val boolDesc: ClassDesc = CD_boolean
}

object NonBoxingTypesConverter {
  def fromAmbientDealiasingCtx(using dealiasingCtx: DealiasingContext): NonBoxingTypesConverter =
    NonBoxingTypesConverter(dealiasingCtx)
}
