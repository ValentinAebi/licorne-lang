package compiler.typing.contexts

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA.{FieldResolutionTarget, InvocationTarget}
import compiler.lang.*
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.NothingType
import compiler.pipeline.CompilationStep
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.contexts.ResolutionContext.{FieldResolResult, FuncResolResult}
import compiler.typing.smartcasting.TypesReasoningCache
import compiler.util.zipCommons

import scala.collection.immutable.SeqMap
import scala.reflect.ClassTag

final case class ResolutionContext(
                                    interfaces: SeqMap[TypeIdentifier, InterfaceSignature],
                                    classes: SeqMap[TypeIdentifier, ClassSignature],
                                    objects: SeqMap[TypeIdentifier, ObjectSignature],
                                    datatypes: SeqMap[TypeIdentifier, DatatypeSignature],
                                    records: SeqMap[TypeIdentifier, RecordSignature],
                                    typeVarsCtx: TypeVariablesContext,
                                    er: ErrorReporter
                                  )(using CompilationStep) {

  val typesReasoningCache: TypesReasoningCache = TypesReasoningCache(this)

  def resolveTypeSig(typeId: TypeIdentifier): Option[TypeSignature] =
    (interfaces.get(typeId)
      orElse classes.get(typeId)
      orElse objects.get(typeId)
      orElse datatypes.get(typeId)
      orElse records.get(typeId))

  def resolveTypeSigAs[S <: TypeSignature : ClassTag](typeId: TypeIdentifier): Option[S] =
    resolveTypeSig(typeId) match {
      case Some(sig: S) => Some(sig)
      case _ => None
    }

  def resolveFunSig(receiver: Type, funId: FunOrVarId, posOpt: Option[Position]): (InvocationTarget, Type) = {

    def errorCase() = {
      er.reportError(s"method $funId not found in type $receiver", posOpt)
      (InvocationTarget.Unresolvable(funId), NothingType)
    }

    receiver.principalType match {
      case NamedType(typeName, typeArgs, args) =>
        resolveFunSig(typeName, funId) match {
          case FuncResolResult.Success(ownerSig, funSig) =>
            val typesSubst = instantiateTypes(typeName, funSig.typeParams, typeArgs, posOpt)
            val instantiatedRetType = funSig.retType.substitute(typesSubst, Map.empty)
            val invocationTarget = InvocationTarget.Resolved(ownerSig, funSig, instantiatedRetType)
            (invocationTarget, instantiatedRetType)
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  def resolveFunSig(receiverId: TypeIdentifier, funId: FunOrVarId): FuncResolResult = {
    resolveTypeSigAs[EncapsulatedTypeSig](receiverId) match {
      case None => FuncResolResult.OwnerNotFound
      case Some(ownerSig) =>
        ownerSig.functions.get(funId) match {
          case None => FuncResolResult.FuncNotFound(ownerSig)
          case Some(funSig) => FuncResolResult.Success(ownerSig, funSig)
        }
    }
  }

  def resolveFieldAccess(owner: Type, fieldId: FunOrVarId, posOpt: Option[Position]): (FieldResolutionTarget, Type) = {

    def errorCase() = {
      er.reportError(s"field $fieldId not found in type ${owner.principalType}", posOpt)
      (FieldResolutionTarget.Unresolvable(fieldId), NothingType)
    }

    owner.principalType match {
      case NamedType(typeName, typeArgs, args) =>
        resolveFieldAccess(typeName, fieldId) match {
          case FieldResolResult.Success(ownerSig, field) =>
            val typeSubst = instantiateTypes(ownerSig.id, ownerSig.typeParams, typeArgs, posOpt)
            val instantiatedFieldType = field.tpe.substitute(typeSubst, Map.empty)
            (FieldResolutionTarget.Resolved(ownerSig, fieldId, instantiatedFieldType), instantiatedFieldType)
          case _ => errorCase()
        }
      case _ => errorCase()
    }
  }

  def resolveFieldAccess(ownerId: TypeIdentifier, fieldId: FunOrVarId): FieldResolResult = {
    resolveTypeSigAs[UserInstantiableTypeSig](ownerId) match {
      case None => FieldResolResult.OwnerNotFound
      case Some(ownerSig) =>
        ownerSig.fields.get(fieldId) match {
          case None => FieldResolResult.FieldNotFound(ownerSig)
          case Some(field) => FieldResolResult.Success(ownerSig, field)
        }
    }
  }

  def declarationPositionOf(tid: TypeIdentifier): Option[Position] =
    resolveTypeSig(tid).flatMap(_.declPosOpt)

  private def instantiateTypes(tid: TypeIdentifier, typeParams: List[TypeParamInfo], typeArgs: List[Type], posOpt: Option[Position]): Map[TypeIdentifier, Type] = {
    if typeParams.size == typeArgs.size then typeParams.map(_.tid).zip(typeArgs).toMap
    else {
      if (typeArgs.nonEmpty) {
        er.reportError(s"wrong number of type parameters for type $tid", posOpt)
      }
      Map.from(for tp <- typeParams yield tp.tid -> typeVarsCtx.newTypeVariable(tp.tid.stringId, posOpt))
    }
  }

}

object ResolutionContext {

  def apply(program: Program, typeVarsCtx: TypeVariablesContext, er: ErrorReporter)
           (using CompilationStep): ResolutionContext =
    ResolutionContext(
      program.interfaces,
      program.classes,
      program.objects,
      program.datatypes,
      program.records,
      typeVarsCtx,
      er
    )

  enum FuncResolResult {
    case OwnerNotFound
    case FuncNotFound(ownerSig: EncapsulatedTypeSig)
    case Success(ownerSig: EncapsulatedTypeSig, funSig: FunctionSignature)

    def forceGetFunSig: FunctionSignature = this match {
      case Success(_, funSig) => funSig
      case _ => throw UnsupportedOperationException("function resolution failed")
    }
  }

  enum FieldResolResult {
    case OwnerNotFound
    case FieldNotFound(ownerSig: UserInstantiableTypeSig)
    case Success(ownerSig: UserInstantiableTypeSig, field: Field)

    def ifSuccess(action: FieldResolResult.Success => Unit): Unit = this match {
      case success: FieldResolResult.Success =>
        action(success)
      case _ => ()
    }
  }

}
