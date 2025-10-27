package lang

import identifiers.*
import lang.Capturables.*
import lang.Types.Type

import scala.collection.mutable

final case class FunctionSignature(
                                    name: FunOrVarId,
                                    args: List[(Option[FunOrVarId], Type)],
                                    retType: Type,
                                    visibility: Visibility
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
                                 paramImports: mutable.LinkedHashMap[FunOrVarId, FieldInfo],
                                 importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                 importedDevices: mutable.LinkedHashSet[Device],
                                 functions: Map[FunOrVarId, FunctionSignature]
                               )
  extends TypeSignature, ConstructibleSig, UserConstructibleSig, ImporterSig, SelectableSig, FunctionsProviderSig {

  override def isAbstract: Boolean = false
}

final case class PackageSignature(
                                   id: TypeIdentifier,
                                   importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                   importedDevices: mutable.LinkedHashSet[Device],
                                   functions: Map[FunOrVarId, FunctionSignature]
                                 ) extends TypeSignature, ConstructibleSig, ImporterSig, FunctionsProviderSig {
  override def isAbstract: Boolean = false
}

final case class StructSignature(
                                  id: TypeIdentifier,
                                  fields: mutable.LinkedHashMap[FunOrVarId, FieldInfo],
                                  directSupertypes: Seq[TypeIdentifier],
                                  directSubtypesOpt: Option[mutable.LinkedHashSet[TypeIdentifier]]
                                )
  extends TypeSignature, ConstructibleSig, UserConstructibleSig, SelectableSig {
  override def isAbstract: Boolean = directSubtypesOpt.isDefined
}

final case class FieldInfo(tpe: Type, isReassignable: Boolean)
