package compiler.backend

import identifiers.{FunOrVarId, TypeIdentifier}
import lang.*
import lang.Types.{PrimitiveTypeShape, Type, TypeShape}
import lang.Values.Value

import scala.collection.mutable

object DescriptorsCreator {

  /**
   * @return JVM descriptor for [[tpe]]
   */
  def descriptorForType(tpe: TypeShape)(using typeResolver: TypeIdentifier => RuntimeTypeSignature): String = {
    tpe match
      case PrimitiveTypeShape.IntType => "I"
      case PrimitiveTypeShape.DoubleType => "D"
      case PrimitiveTypeShape.CharType => "C"
      case PrimitiveTypeShape.BoolType => "Z"
      case PrimitiveTypeShape.StringType => "Ljava/lang/String;"
      case PrimitiveTypeShape.VoidType => "V"
      case PrimitiveTypeShape.NothingType => "V"
      case Types.NamedTypeShape(typeName, _, _) if !typeResolver(typeName).isAbstract => s"L$typeName;"
      case _: Types.NamedTypeShape => "Ljava/lang/Object;"
      case Types.UndefinedTypeShape => assert(false)
  }

  /**
   * @return JVM descriptor for [[funSig]]
   */
  def descriptorForFunc(argTypes: mutable.LinkedHashMap[Value, Type], retType: Type)(using typeResolver: TypeIdentifier => RuntimeTypeSignature): String = {
    argTypes.map((_, tpe) => descriptorForType(tpe.shape)).mkString("(", "", ")") ++ descriptorForType(retType.shape)
  }
  
  def descriptorForFunc(funSig: FunctionSignature)(using typeResolver: TypeIdentifier => RuntimeTypeSignature): String =
    descriptorForFunc(funSig.params, funSig.retType)

}
