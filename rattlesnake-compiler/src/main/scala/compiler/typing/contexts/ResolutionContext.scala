package compiler.typing.contexts

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.*
import compiler.lang.Types.*
import compiler.program.Program
import compiler.reporting.Position
import compiler.typing.contexts.ResolutionContext.FuncResolResult
import compiler.typing.contexts.ResolutionContext.FuncResolResult.*
import compiler.typing.smartcasting.TypesReasoningCache
import compiler.util.zipCommons

import scala.reflect.ClassTag

final case class ResolutionContext(
                                    interfaces: Map[TypeIdentifier, InterfaceSignature],
                                    classes: Map[TypeIdentifier, ClassSignature],
                                    objects: Map[TypeIdentifier, ObjectSignature],
                                    datatypes: Map[TypeIdentifier, DatatypeSignature],
                                    records: Map[TypeIdentifier, RecordSignature]
                                  ) {

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

  def resolveFunSig(ownerId: TypeIdentifier, funId: FunOrVarId): FuncResolResult = {
    resolveTypeSigAs[Encapsulated](ownerId) match {
      case None => OwnerNotFound
      case Some(ownerSig) =>
        ownerSig.functions.get(funId) match {
          case None => FuncNotFound(ownerSig)
          case Some(funSig) => Success(ownerSig, funSig)
        }
    }
  }

  def declarationPositionOf(tid: TypeIdentifier): Option[Position] =
    resolveTypeSig(tid).flatMap(_.declPosOpt)

}

object ResolutionContext {

  def fromProgram(program: Program): ResolutionContext = ResolutionContext(
    program.interfaces,
    program.classes,
    program.objects,
    program.datatypes,
    program.records
  )

  enum FuncResolResult {
    case OwnerNotFound
    case FuncNotFound(ownerSig: Encapsulated)
    case Success(ownerSig: Encapsulated, funSig: FunctionSignature)

    def forceGetFunSig: FunctionSignature = this match {
      case Success(_, funSig) => funSig
      case _ => throw UnsupportedOperationException("function resolution failed")
    }
  }

}
