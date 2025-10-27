package compiler.backend

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.*
import lang.Types.{PrimitiveTypeShape, Type, TypeShape}

object DescriptorsCreator {

  /**
   * @return JVM descriptor for [[tpe]]
   */
  def descriptorForType(tpe: TypeShape)(using typeResolver: TypeIdentifier => TypeSignature): String = {
    tpe match
      case PrimitiveTypeShape.IntType => "I"
      case PrimitiveTypeShape.DoubleType => "D"
      case PrimitiveTypeShape.CharType => "C"
      case PrimitiveTypeShape.BoolType => "Z"
      case PrimitiveTypeShape.StringType => "Ljava/lang/String;"
      case PrimitiveTypeShape.VoidType => "V"
      case PrimitiveTypeShape.NothingType => "V"
      case Types.NamedTypeShape(typeName) if !typeResolver(typeName).isAbstract => s"L$typeName;"
      case Types.NamedTypeShape(_) => "Ljava/lang/Object;"
      case Types.UndefinedTypeShape => assert(false)
  }

  /**
   * @return JVM descriptor for [[funSig]]
   */
  def descriptorForFunc(argTypes: List[(Option[FunOrVarId], Type)], retType: Type)(using typeResolver: TypeIdentifier => TypeSignature): String = {
    argTypes.map((_, tpe) => descriptorForType(tpe.shape)).mkString("(", "", ")") ++ descriptorForType(retType.shape)
  }
  
  def descriptorForFunc(funSig: FunctionSignature)(using typeResolver: TypeIdentifier => TypeSignature): String =
    descriptorForFunc(funSig.args, funSig.retType)

}
