package compiler.backend

import compiler.analysisctx.AnalysisContext
import identifiers.FunOrVarId
import lang.*
import lang.Types.{PrimitiveTypeShape, Type, TypeShape}

object DescriptorsCreator {

  /**
   * @return JVM descriptor for [[tpe]]
   */
  def descriptorForType(tpe: TypeShape)(using ctx: AnalysisContext): String = {
    tpe match
      case PrimitiveTypeShape.IntType => "I"
      case PrimitiveTypeShape.DoubleType => "D"
      case PrimitiveTypeShape.CharType => "C"
      case PrimitiveTypeShape.BoolType => "Z"
      case PrimitiveTypeShape.StringType => "Ljava/lang/String;"
      case PrimitiveTypeShape.VoidType => "V"
      case PrimitiveTypeShape.NothingType => "V"
      case Types.NamedTypeShape(typeName) if !ctx.resolveType(typeName).get.isAbstract => s"L$typeName;"
      case Types.NamedTypeShape(_) | Types.UnionTypeShape(_) => "Ljava/lang/Object;"
      case Types.ArrayTypeShape(elemType) => s"[${descriptorForType(elemType.shape)}"
      case Types.UndefinedTypeShape => assert(false)
  }

  /**
   * @return JVM descriptor for [[funSig]]
   */
  def descriptorForFunc(argTypes: List[(Option[FunOrVarId], Type)], retType: Type)(using AnalysisContext): String = {
    argTypes.map((_, tpe) => descriptorForType(tpe.shape)).mkString("(", "", ")") ++ descriptorForType(retType.shape)
  }
  
  def descriptorForFunc(funSig: FunctionSignature)(using AnalysisContext): String =
    descriptorForFunc(funSig.args, funSig.retType)

}
