package lang

import identifiers.*
import lang.Capturables.*
import lang.CaptureDescriptors.CaptureSet
import lang.Types.PrimitiveTypeShape.VoidType
import lang.Types.{NamedTypeShape, PrimitiveTypeShape, Type}
import lang.Visibility.Public

import scala.collection.mutable

final case class FunctionSignature(
                                    name: FunOrVarId,
                                    args: List[(Option[FunOrVarId], Type)],
                                    retType: Type,
                                    visibility: Visibility
                                  )

sealed trait TypeSignature {
  def id: TypeIdentifier

  def getNonSubstitutedCaptureDescr: CaptureSet

  def isAbstract: Boolean
}

sealed trait FunctionsProviderSig extends TypeSignature {
  def functions: Map[FunOrVarId, FunctionSignature]
}

sealed trait ConstructibleSig extends TypeSignature {

  def params: mutable.LinkedHashMap[FunOrVarId, FieldInfo]

  def globalCaptures: Set[ConcreteCapturable]

  def voidInitMethodSig: FunctionSignature =
    FunctionSignature(ConstructorFunId, params.toList.map((id, info) => (Some(id), info.tpe)), VoidType, Public)
}

sealed trait UserConstructibleSig extends TypeSignature {
  this: ConstructibleSig =>
}

sealed trait SelectableSig extends TypeSignature {
  this: ConstructibleSig =>

  def typeOfSelectIfCapturable(sel: FunOrVarId): Option[Type] =
    params.get(sel)
      .filter(!_.isReassignable)
      .map(_.tpe)
}

sealed trait ImporterSig extends TypeSignature {

  def paramImports: mutable.LinkedHashMap[FunOrVarId, Type]

  def importedPackages: mutable.LinkedHashSet[TypeIdentifier]

  def importedDevices: mutable.LinkedHashSet[Device]

  def globalCaptures: Set[ConcreteCapturable] =
    importedPackages.map(CapPackage(_)).toSet ++ importedDevices.map(CapDevice(_))
  
  def globalCapturesAsCs: CaptureSet = CaptureSet(globalCaptures.toSet: Set[Capturable])

  def params: mutable.LinkedHashMap[FunOrVarId, FieldInfo] =
    paramImports.map((id, tpe) => id -> FieldInfo(tpe, isReassignable = false))
}

final case class ModuleSignature(
                                  id: TypeIdentifier,
                                  paramImports: mutable.LinkedHashMap[FunOrVarId, Type],
                                  importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                  importedDevices: mutable.LinkedHashSet[Device],
                                  functions: Map[FunOrVarId, FunctionSignature]
                                )
  extends TypeSignature, ConstructibleSig, UserConstructibleSig, ImporterSig, SelectableSig, FunctionsProviderSig {

  override def getNonSubstitutedCaptureDescr: CaptureSet =
    CaptureSet((globalCaptures.toSet: Set[Capturable]) ++ paramImports.map((paramId, _) => MePath.dot(paramId)))

  override def isAbstract: Boolean = false
}

final case class PackageSignature(
                                   id: TypeIdentifier,
                                   importedPackages: mutable.LinkedHashSet[TypeIdentifier],
                                   importedDevices: mutable.LinkedHashSet[Device],
                                   functions: Map[FunOrVarId, FunctionSignature]
                                 ) extends TypeSignature, ConstructibleSig, ImporterSig, FunctionsProviderSig {

  override def paramImports: mutable.LinkedHashMap[FunOrVarId, Type] = mutable.LinkedHashMap.empty

  override def getNonSubstitutedCaptureDescr: CaptureSet = globalCapturesAsCs

  def asType: Type = NamedTypeShape(id) ^ globalCapturesAsCs

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

  override def params: mutable.LinkedHashMap[FunOrVarId, FieldInfo] = fields

  override def getNonSubstitutedCaptureDescr: CaptureSet = CaptureDescriptors.unionOf(
    fields.filter((_, info) => !info.tpe.captureDescriptor.isEmpty)
      .map { (id, info) =>
        if info.isReassignable
        then info.tpe.captureDescriptor
        else CaptureSet(MePath.dot(id))
      }
  )

  override def globalCaptures: Set[ConcreteCapturable] = Set.empty
}

final case class FieldInfo(tpe: Type, isReassignable: Boolean)
