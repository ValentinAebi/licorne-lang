package compiler.typing.contexts

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.lang.{RuntimeTypeSignature, TypeTypeParamInfo}
import compiler.lang.Types.{NamedType, Type}
import compiler.typing.contexts.SubtypingContext.SupertypesSubst

import scala.collection.mutable

final class SubtypingContext(resolutionCtx: ResolutionContext, subtypingGraph: Graph[TypeIdentifier]) {
  private val flattenedSupertypesSubstitutions: SupertypesSubst = mutable.LinkedHashMap.empty

  def subToSuperSubst(subT: TypeIdentifier, superT: TypeIdentifier): Option[Map[TypeIdentifier, Type]] = {
    if subT == superT then resolutionCtx.resolveSignatureAs[RuntimeTypeSignature](subT).map {
      _.typeParams.map {
        case TypeTypeParamInfo(tid, variance, upperBounds, lowerBounds) =>
          tid -> NamedType(tid, List.empty, List.empty)
      }.toMap
    } else for {
      subTSupers <- flattenedSupertypesSubstitutions.get(subT)
      superSubst <- subTSupers.get(superT)
    } yield superSubst
  }
  
}

object SubtypingContext {

  type SupertypesSubst = mutable.LinkedHashMap[TypeIdentifier, mutable.LinkedHashMap[TypeIdentifier, Map[TypeIdentifier, Type]]]
  
}
