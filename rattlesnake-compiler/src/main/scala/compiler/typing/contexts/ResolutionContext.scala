package compiler.typing.contexts

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.*
import compiler.pipeline.CompilationStep
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.contexts.ResolutionContext.{FieldResolResult, FuncResolResult}
import compiler.typing.smartcasting.TypesReasoningCache

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

  def resolveFunSig(receiverId: TypeIdentifier, funId: FunOrVarId)
                   (using subtypingCtx: SubtypingContext): FuncResolResult = {
    resolveTypeSigAs[EncapsulatedTypeSig](receiverId) match {
      case None => FuncResolResult.OwnerNotFound
      case Some(ownerSig) =>
        ownerSig.functions.get(funId) match {
          case Some(funSig) => FuncResolResult.Success(ownerSig, funSig)
          case None =>
            ownerSig.directSupertypes.iterator.map { superT =>
              resolveFunSig(superT.typeName, funId) match {
                case FuncResolResult.Success(superOwnerSig, superFunSig) =>
                  val subst = subtypingCtx.subToSuperSubst(receiverId, superT.typeName).get
                  FuncResolResult.Success(ownerSig, superFunSig.substitute(receiverId, subst))
                case failure => failure
              }
            }.find(_.isInstanceOf[FuncResolResult.Success])
            .getOrElse(FuncResolResult.FuncNotFound(ownerSig))
        }
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
    
    def asOption: Option[FunctionSignature] = this match {
      case Success(ownerSig, funSig) => Some(funSig)
      case _ => None
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
