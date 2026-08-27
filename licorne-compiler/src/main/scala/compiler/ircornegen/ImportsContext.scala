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
    case TypeIdentifier(Nil, nonPrefixedId) => 
      importedTypeFor(nonPrefixedId).getOrElse(tid)
    case tid => tid
  }

  def importedFuncFor(funId: FunOrVarId): Option[(TypeIdentifier, FunOrVarId)] =
    importedFunctions.get(funId)

}
