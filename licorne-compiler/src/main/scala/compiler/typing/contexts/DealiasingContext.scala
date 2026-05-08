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
        case Some(TypeAliasSignature(id, typeParams, thisValue, params, rhs, sigScope, declPosOpt)) =>
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
    case RefinedType(baseType, predicate) =>
      RefinedType(dealiasType(baseType), predicate)
    case intRangeType: IntRangeType => intRangeType
    case NullableType(nullatedType) =>
      NullableType(dealiasType(nullatedType))
  }

  /**
   * "value type" means "a type that is not a reference"
   */
  def isValueType(tpe: Type): Boolean = dealiasType(tpe) match {
    case IntType | DoubleType | CharType | BoolType | StringType | UnitType | NothingType => true
    case NullType | AnyType => false
    case NamedType(typeName, typeArgs, args) => false
    case ClosureType(params, result, enforcedPure) => false
    case tv: TypeVariable =>
      tv.actualTypeIfResolved.exists(isValueType)
    case UnionType(types) =>
      types.forall(isValueType)
    case IntersectionType(types) =>
      types.exists(isValueType)
    case RefinedType(baseType, predicate) =>
      isValueType(baseType)
    case IntRangeType(lowerBoundOpt, upperBoundOpt) => true
    case NullableType(nullatedType) =>
      isValueType(nullatedType)
  }

  def eraseRefinements(tpe: Type): Type = dealiasType(tpe) match {
    case primitiveType: PrimitiveType => primitiveType
    case IntRangeType(lowerBoundOpt, upperBoundOpt) => IntType
    case NullableType(nullatedType) => nullatedType
    case NamedType(typeName, typeArgs, args) =>
      NamedType(typeName, typeArgs.map(eraseRefinements), List.empty)
    case ClosureType(params, result, enforcedPure) =>
      ClosureType(params.map(eraseRefinements), eraseRefinements(result), enforcedPure)
    case tv: TypeVariable => tv.actualTypeIfResolved.orElse(tv.upperBoundOpt) match {
      case Some(tpe) => eraseRefinements(tpe)
      case None => AnyType
    }
    case RefinedType(baseType, predicate) => eraseRefinements(baseType)
    case UnionType(types) =>
      if types.size == 1
      then eraseRefinements(types.head)
      else AnyType
    case IntersectionType(types) =>
      if types.isEmpty
      then AnyType
      else eraseRefinements(types.head)
  }
  
}
