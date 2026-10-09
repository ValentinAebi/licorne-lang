package compiler.typing.contexts

import compiler.identifiers.TypeIdentifier
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.lang.{TypeAliasSignature, Types}


final case class DealiasingContext(typeAliases: Map[TypeIdentifier, TypeAliasSignature]) {

  // TODO memoize recursive multi-step dealiasing (update the signatures in the mapping)

  def dealiasType(tpe: Type): Type = tpe match {
    case primitiveType: Types.PrimitiveType => primitiveType
    case NamedType(typeName, typeArgsRaw, args) =>
      val typeArgsSubst = typeArgsRaw.map(dealiasType)
      typeAliases.get(typeName) match {
        case Some(TypeAliasSignature(id, typeParams, params, rhs, visibility, sigScope, declPosOpt)) =>
          val typesSubst =
            typeParams.map(_.tid)
              .zip(typeArgsSubst)
              .toMap
          val valsSubst = params.map {
            case (paramId, (paramType, paramVal)) => paramVal
          }.zip(args).toMap
          dealiasType(rhs.substitute(typesSubst, valsSubst))
        case None => NamedType(typeName, typeArgsSubst, args)
      }
    case ClosureType(params, result, enforcedPure) =>
      ClosureType(params.map(dealiasType), dealiasType(result), enforcedPure)
    case typeVar: Types.TypeVariable => typeVar
    case UnionType(types) =>
      UnionType(types.map(dealiasType))
    case IntersectionType(types) =>
      IntersectionType(types.map(dealiasType))
    case TernaryType(cond, left, right) =>
      TernaryType(cond, dealiasType(left), dealiasType(right))
    case RefinedType(baseType, predicate) =>
      RefinedType(dealiasType(baseType), predicate)
    case intRangeType: IntRangeType => intRangeType
    case NullableType(nullatedType) =>
      NullableType(dealiasType(nullatedType))
  }
  
}
