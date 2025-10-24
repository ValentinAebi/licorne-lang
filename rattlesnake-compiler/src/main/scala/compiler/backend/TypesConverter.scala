package compiler.backend

import compiler.analysisctx.AnalysisContext
import compiler.backend.DescriptorsCreator.descriptorForType
import identifiers.TypeIdentifier
import lang.Types.*
import lang.Types.PrimitiveTypeShape.DoubleType
import lang.{StructSignature, TypeSignature, Types}
import org.objectweb.asm
import org.objectweb.asm.Opcodes
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.Type.*

object TypesConverter {

  private def safeGetOpcode(tpe: asm.Type, intOpcode: Int): Int = {
    val allowedOpcodes = Set(ILOAD, ISTORE, IALOAD, IASTORE, IADD, ISUB, IMUL, IDIV, IREM, INEG, ISHL, ISHR, IUSHR, IAND, IOR, IXOR, IRETURN)
    require(allowedOpcodes.contains(intOpcode), s"unexpected opcode: $intOpcode")
    tpe.getOpcode(intOpcode)
  }

  def opcodeFor(tpe: Types.TypeShape, intOpcode: Int, refOpcode: => Int): Int = {
    convertToAsmType(tpe).map(safeGetOpcode(_, intOpcode)).getOrElse(refOpcode)
  }

  def convertToAsmType(tpe: Types.TypeShape): Option[asm.Type] = {
    tpe match
      case PrimitiveTypeShape.IntType => INT_TYPE.toSome
      case PrimitiveTypeShape.DoubleType => DOUBLE_TYPE.toSome
      case PrimitiveTypeShape.CharType => CHAR_TYPE.toSome
      case PrimitiveTypeShape.BoolType => BOOLEAN_TYPE.toSome
      case PrimitiveTypeShape.VoidType => VOID_TYPE.toSome
      case PrimitiveTypeShape.NothingType => VOID_TYPE.toSome
      case _: (PrimitiveTypeShape.StringType.type | NamedTypeShape | ArrayTypeShape | UnionTypeShape) => None
      case Types.UndefinedTypeShape => assert(false)
  }

  def convertToAsmTypeCode(tpe: Types.TypeShape): Option[Int] = {
    tpe match
      case PrimitiveTypeShape.IntType => Opcodes.T_INT.toSome
      case PrimitiveTypeShape.DoubleType => Opcodes.T_DOUBLE.toSome
      case PrimitiveTypeShape.CharType => Opcodes.T_CHAR.toSome
      case PrimitiveTypeShape.BoolType => Opcodes.T_BOOLEAN.toSome
      case _ => None
  }

  def internalNameOf(tpe: Types.TypeShape)(using ctx: AnalysisContext): String = {
    tpe match
      case PrimitiveTypeShape.IntType => "I"
      case PrimitiveTypeShape.DoubleType => "D"
      case PrimitiveTypeShape.CharType => "C"
      case PrimitiveTypeShape.BoolType => "Z"
      case PrimitiveTypeShape.StringType => "java/lang/String"
      case PrimitiveTypeShape.VoidType => "V"
      case PrimitiveTypeShape.NothingType => "V"
      case NamedTypeShape(typeName) if !ctx.resolveType(typeName).get.isAbstract => s"$typeName"
      case ArrayTypeShape(elemType) => s"[${descriptorForType(elemType.shape)}"
      case NamedTypeShape(_) | UnionTypeShape(_) => "java/lang/Object"
      case UndefinedTypeShape => assert(false)
  }

  def numSlotsFor(tpe: Types.TypeShape): Int = {
    tpe match
      case DoubleType => 2
      case _ => 1
  }

  extension [T](t: T) private def toSome = Some(t)

}
