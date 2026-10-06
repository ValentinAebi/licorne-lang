package compiler.typing.contexts

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.*
import compiler.lang.Types.Type
import compiler.pipeline.CompilationStep
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.contexts.ResolutionContext.*
import compiler.typing.smartcasting.TypesReasoningCache

import scala.reflect.ClassTag

final case class ResolutionContext(
                                    program: Program,
                                    er: ErrorReporter
                                  )(using CompilationStep) {

  import program.*

  val typesReasoningCache: TypesReasoningCache = TypesReasoningCache(this)

  def resolveTypeSig(typeId: TypeIdentifier): Option[TypeSignature] =
    (interfaces.get(typeId)
      orElse classes.get(typeId)
      orElse objects.get(typeId)
      orElse datatypes.get(typeId)
      orElse records.get(typeId)
      orElse typeAliases.get(typeId))

  def resolveTypeSigAs[S <: TypeSignature : ClassTag](typeId: TypeIdentifier): Option[S] =
    resolveTypeSig(typeId) match {
      case Some(sig: S) => Some(sig)
      case _ => None
    }

  def forceGetFunction(receiverId: TypeIdentifier, descr: FunctionDescriptor): FunctionSignature =
    resolveTypeSigAs[RuntimeTypeSignature](receiverId).get.functions.apply(descr)

  def resolveFunSig(receiverId: TypeIdentifier, descr: FunctionDescriptor, argTypes: Iterable[Type])
                   (using tpCtx: TypeParamsContext, subtypingCtx: SubtypingContext): FuncResolResult = {

    def nArgsThatMatch(params: Iterable[Type], args: Iterable[Type]): Int =
      args.zip(params).count(subtypingCtx.isSubtype(_, _))

    def functionScore(funSig: FunctionSignature): Int =
      nArgsThatMatch(funSig.paramsWithoutThis.map(_._2), argTypes) * 2 + (if funSig.isPure then 1 else 0)

    resolveTypeSigAs[RuntimeTypeSignature](receiverId) match {
      case None => FuncResolResult.OwnerNotFound
      case Some(ownerSig) =>
        ownerSig.functions.get(descr) match {
          case Some(funSig) => FuncResolResult.Success(ownerSig, funSig)
          case None =>
            ownerSig.directSupertypes.flatMap { superT =>
              resolveFunSig(superT.typeName, descr, argTypes).asOptionWithReceiver
                .map { (superOwnerSig, superFunSig) =>
                  val subst = subtypingCtx.subToSuperSubst(receiverId, superT.typeName).get
                  (ownerSig, superFunSig.substitute(receiverId, subst))
                }
            }.maxByOption((tSig, funSig) => functionScore(funSig)) match {
              case Some(tSig, funSig) => FuncResolResult.Success(tSig, funSig)
              case None => FuncResolResult.FuncNotFound(ownerSig)
            }
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

  enum FuncResolResult {
    case OwnerNotFound
    case FuncNotFound(ownerSig: RuntimeTypeSignature)
    case Success(ownerSig: RuntimeTypeSignature, funSig: FunctionSignature)

    def forceGetFunSig: FunctionSignature = this match {
      case Success(_, funSig) => funSig
      case _ => throw UnsupportedOperationException("function resolution failed")
    }

    def asOptionWithoutReceiver: Option[FunctionSignature] = this match {
      case Success(ownerSig, funSig) => Some(funSig)
      case _ => None
    }

    def asOptionWithReceiver: Option[(RuntimeTypeSignature, FunctionSignature)] = this match {
      case Success(ownerSig, funSig) => Some(ownerSig, funSig)
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
