package lang

import identifiers.*
import lang.Values.Value
import lang.Types.Type

import scala.collection.mutable

final case class FunctionSignature(
                                    name: FunOrVarId,
                                    typeParams: List[TypeIdentifier],
                                    params: mutable.LinkedHashMap[Value, Type],
                                    retType: Type,
                                    visibility: Visibility
                                  )

sealed trait TypeSignature {
  def id: TypeIdentifier
}

final case class TypeAliasSignature(
                                     id: TypeIdentifier,
                                     typeParams: List[TypeIdentifier],
                                     params: mutable.LinkedHashMap[FunOrVarId, TypeIdentifier]
                                   ) extends TypeSignature

sealed trait RuntimeTypeSignature extends TypeSignature {
  def isAbstract: Boolean
}

sealed trait FunctionsProviderSig extends RuntimeTypeSignature {
  def functions: Map[FunOrVarId, FunctionSignature]
}

sealed trait ConstructibleSig extends RuntimeTypeSignature {

}

sealed trait UserConstructibleSig extends RuntimeTypeSignature {
  this: ConstructibleSig =>
  
  def typeParams: List[(TypeIdentifier, Variance)]
}

sealed trait SelectableSig extends RuntimeTypeSignature {
  this: ConstructibleSig =>
}

sealed trait ImporterSig extends RuntimeTypeSignature {

}

final case class ClassSignature(
                                 id: TypeIdentifier,
                                 typeParams: List[(TypeIdentifier, Variance)],
                                 paramImports: mutable.LinkedHashMap[FunOrVarId, ClassFieldInfo],
                                 importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                 functions: Map[FunOrVarId, FunctionSignature]
                               )
  extends RuntimeTypeSignature, ConstructibleSig, UserConstructibleSig, ImporterSig, SelectableSig, FunctionsProviderSig {

  override def isAbstract: Boolean = false
}

final case class ClassFieldInfo(tpe: Type, isReassignable: Boolean)

final case class PackageSignature(
                                   id: TypeIdentifier,
                                   importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                   functions: Map[FunOrVarId, FunctionSignature]
                                 ) extends RuntimeTypeSignature, ConstructibleSig, ImporterSig, FunctionsProviderSig {
  override def isAbstract: Boolean = false
}

final case class StructSignature(
                                  id: TypeIdentifier,
                                  typeParams: List[(TypeIdentifier, Variance)],
                                  fields: mutable.LinkedHashMap[FunOrVarId, Type],
                                  directSupertypes: Seq[TypeIdentifier],
                                  directSubtypesOpt: Option[mutable.LinkedHashSet[TypeIdentifier]]
                                )
  extends RuntimeTypeSignature, ConstructibleSig, UserConstructibleSig, SelectableSig {
  override def isAbstract: Boolean = directSubtypesOpt.isDefined
}
