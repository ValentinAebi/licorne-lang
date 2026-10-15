package compiler.typing.contexts

import compiler.identifiers.TypeIdentifier
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.*
import compiler.lang.{TypeAliasSignature, Types}


final case class DealiasingContext(typeAliases: Map[TypeIdentifier, TypeAliasSignature]) {

  // TODO memoize recursive multi-step dealiasing (update the signatures in the mapping)

  def dealiasType(tpe: Type, dealiasOpaque: Boolean = false): Type =
    tpe.applyRecursivelyToTypes {
      case NamedType(typeName, typeArgs, args) =>
        typeAliases.get(typeName) match {
          case Some(TypeAliasSignature(id, typeParams, params, rhs, visibility, isOpaque, sigScope, declPosOpt)) if !isOpaque || dealiasOpaque =>
            val typesSubst =
              typeParams.map(_.tid)
                .zip(typeArgs)
                .toMap
            val valsSubst = params.map {
              case (paramId, (paramType, paramVal)) => paramVal
            }.zip(args).toMap
            dealiasType(rhs.substitute(typesSubst, valsSubst))
          case _ => NamedType(typeName, typeArgs, args)
        }
    }
  
}
