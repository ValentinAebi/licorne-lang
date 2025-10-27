package lang

import identifiers.*
import lang.Capturables.*
import lang.Types.Type

import scala.collection.mutable

final case class FunctionSignature(
                                    name: FunOrVarId,
                                    typeParams: List[TypeIdentifier],
                                    args: mutable.LinkedHashMap[FunOrVarId, Type],
                                    retType: Type,
                                    visibility: Visibility
                                  )

final case class TypeAliasSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[TypeIdentifier],
                                     params: mutable.LinkedHashMap[FunOrVarId, TypeIdentifier]
                                   )

sealed trait TypeSignature {
  def id: TypeIdentifier

  def isAbstract: Boolean
}

sealed trait FunctionsProviderSig extends TypeSignature {
  def functions: Map[FunOrVarId, FunctionSignature]
}

sealed trait ConstructibleSig extends TypeSignature {

}

sealed trait UserConstructibleSig extends TypeSignature {
  this: ConstructibleSig =>
}

sealed trait SelectableSig extends TypeSignature {
  this: ConstructibleSig =>
}

sealed trait ImporterSig extends TypeSignature {

}

final case class ClassSignature(
                                 id: TypeIdentifier,
                                 typeParams: List[TypeIdentifier],
                                 paramImports: mutable.LinkedHashMap[FunOrVarId, ClassFieldInfo],
                                 importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                 functions: Map[FunOrVarId, FunctionSignature]
                               )
  extends TypeSignature, ConstructibleSig, UserConstructibleSig, ImporterSig, SelectableSig, FunctionsProviderSig {

  override def isAbstract: Boolean = false
}

final case class ClassFieldInfo(tpe: Type, isReassignable: Boolean)

final case class PackageSignature(
                                   id: TypeIdentifier,
                                   typeParams: List[TypeIdentifier],
                                   importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                   functions: Map[FunOrVarId, FunctionSignature]
                                 ) extends TypeSignature, ConstructibleSig, ImporterSig, FunctionsProviderSig {
  override def isAbstract: Boolean = false
}

final case class StructSignature(
                                  id: TypeIdentifier,
                                  typeParams: List[TypeIdentifier],
                                  fields: mutable.LinkedHashMap[FunOrVarId, Type],
                                  directSupertypes: Seq[TypeIdentifier],
                                  directSubtypesOpt: Option[mutable.LinkedHashSet[TypeIdentifier]]
                                )
  extends TypeSignature, ConstructibleSig, UserConstructibleSig, SelectableSig {
  override def isAbstract: Boolean = directSubtypesOpt.isDefined
}
