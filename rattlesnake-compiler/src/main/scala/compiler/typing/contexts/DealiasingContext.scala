package compiler.typing.contexts

import compiler.identifiers.TypeIdentifier
import compiler.lang.Types.*
import compiler.lang.{TypeAliasSignature, Types}
import compiler.util.zipCommons

final case class DealiasingContext(typeAliases: Map[TypeIdentifier, TypeAliasSignature]) {

  def dealiasType(tpe: Type): Type = tpe match {
    case primitiveType: Types.PrimitiveType => primitiveType
    case NamedType(typeName, typeArgsRaw, args) =>
      val typeArgsSubst = typeArgsRaw.map(dealiasType)
      typeAliases.get(typeName) match {
        case Some(TypeAliasSignature(id, typeParams, thisValue, params, rhs, declPosOpt)) =>
          val typesSubst =
            typeParams.map(_.tid)
              .zipCommons(typeArgsSubst)
              .toMap
          val valsSubst = params.map {
            case (paramId, (paramType, paramVal)) => paramVal
          }.zipCommons(args).toMap
          dealiasType(rhs.substitute(typesSubst, valsSubst))
        case None => NamedType(typeName, typeArgsSubst, args)
      }
    case ClosureType(params, result) =>
      ClosureType(params.map(dealiasType), dealiasType(result))
    case typeVar: Types.TypeVariable => typeVar
    case UnionType(types) =>
      UnionType(types.map(dealiasType))
    case IntersectionType(types) =>
      IntersectionType(types.map(dealiasType))
    case intRangeType: IntRangeType => intRangeType
  }
  
}
