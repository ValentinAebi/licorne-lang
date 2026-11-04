package compiler.ircornegen

import compiler.identifiers.{FunOrVarId, TypeIdentifier}

import scala.collection.immutable.SeqMap


final case class ImportsContext(
                                 importedTypes: SeqMap[String, TypeIdentifier],
                                 importedFunctions: SeqMap[FunOrVarId, (TypeIdentifier, FunOrVarId)]
                               ) {

  def importedTypeFor(typeName: String): Option[TypeIdentifier] =
    importedTypes.get(typeName)
    
  def applyImports(tid: TypeIdentifier): TypeIdentifier = tid match {
    case TypeIdentifier(Nil, nonPrefixedId, isCompanionObject) =>
      val raw = importedTypeFor(nonPrefixedId).getOrElse(tid)
      if isCompanionObject then raw.asCompanionId else raw
    case tid => tid
  }

  def importedFuncFor(funId: FunOrVarId): Option[(TypeIdentifier, FunOrVarId)] =
    importedFunctions.get(funId)

}
