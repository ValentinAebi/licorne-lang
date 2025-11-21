package compiler.typechecking

import compiler.analysisctx.AnalysisContext
import identifiers.TypeIdentifier
import lang.Types.*
import lang.Values.And
import lang.{TypeAliasSignature, Types, Variance}

import scala.collection.mutable

final class TypeCheckingContext(val analysisContext: AnalysisContext) {
  private val typeParams = mutable.Map.empty[TypeIdentifier, Variance]
  
  def desugarType(tpe: Type): Type = {
    val desugaredType = tpe match {
      case RefinedType(baseTypeRaw, itValueRaw, predicateRaw) =>
        desugarType(baseTypeRaw) match {
          case RefinedType(baseTypeDes, itValueDes, predicateDes) =>
            RefinedType(baseTypeDes, itValueRaw, And(predicateRaw, predicateDes.substitute(Map(itValueDes -> itValueRaw))))
          case baseTypeDes: BaseType =>
            RefinedType(baseTypeDes, itValueRaw, predicateRaw)
        }
      case primitiveType: Types.PrimitiveType => primitiveType
      case Types.NamedType(typeName, typeArgs, args, isPure) =>
        analysisContext.typeAliases.get(typeName) match {
          case Some(TypeAliasSignature(id, typeParams, thisValue, params, rhs)) =>
            val typesSubst = typeParams.map((id, variance) => id).zipCommons(typeArgs).toMap
            val valsSubst = params.map {
              case (paramId, (paramType, paramVal)) => paramVal
            }.zipCommons(args).toMap
            rhs.substitute(typesSubst, valsSubst)
          case None => tpe
        }
      case typeVar: Types.TypeVar => typeVar
    }
    if desugaredType == tpe then tpe
    else desugarType(desugaredType)
  }
  
  extension[T](l: Iterable[T]) private def zipCommons[U](r: Iterable[U]): Iterable[(T, U)] =
    l.take(r.size).zip(r.take(l.size))
  
}
