package compiler.typechecking

import compiler.pipeline.CompilationStep.TypeChecking
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import lang.Types.*
import lang.Types.PrimitiveType.*
import lang.{RuntimeTypeSignature, Variance}

import scala.util.boundary

object BaseSubtypeRelation {

  def enforceSubtypingConstraint(subT: Type, superT: Type)
                                (using positionDescr: String, posOpt: Option[Position], er: ErrorReporter, program: Program): Unit =
    enforceSubtypingConstraintInternal(subT, superT)(using ErrorMessage(s"$positionDescr: expected $superT, found $subT"))

  private def enforceSubtypingConstraintInternal(subT: Type, superT: Type)
                                                (using errorMsg: ErrorMessage, posOpt: Option[Position], er: ErrorReporter, program: Program): Boolean = {
    (program.desugarType(subT), program.desugarType(superT)) match {
      case (subT: TypeVariable, superT) =>
        subT.tryToResolve(superT)
        true
      case (subT, superT: TypeVariable) =>
        superT.tryToResolve(subT)
        true
      case (subT, superT) =>
        enforceSubtypingConstraintOnDesugaredBaseTypes(subT.baseType, superT.baseType)
    }
  }

  private def enforceSubtypingConstraintOnDesugaredBaseTypes(subT: BaseType, superT: BaseType)
                                                            (using errorMsg: ErrorMessage, posOpt: Option[Position], er: ErrorReporter, program: Program): Boolean = {
    (subT, superT) match {
      case (subT, superT) if subT.trivialSubtypeOf(superT) => true
      case (NamedType(subtypeName, subtypeTypeArgs, subtypeArgs), NamedType(supertypeName, supertypeTypeArgs, supertypeArgs)) =>
        assert(subtypeArgs.isEmpty)
        assert(supertypeArgs.isEmpty)
        program.subToSuperSubst(subtypeName, supertypeName) match {
          case None =>
            reportNotSubtype(subT, superT)
          case Some(declSubtypingSubst) =>
            val supertypeSig = program.resolveSignatureAs[RuntimeTypeSignature](supertypeName).get
            val subtypeSig = program.resolveSignatureAs[RuntimeTypeSignature](subtypeName).get
            val siteSubst = (subtypeSig.typeParams.map(_._1) zip subtypeTypeArgs).toMap
            val composedSubst = declSubtypingSubst.map {
              case (declSuperTypeTypeArgId, declSubTypeType: NamedType) if declSubTypeType.isSimpleName =>
                declSuperTypeTypeArgId -> siteSubst.getOrElse(declSubTypeType.typeName, declSubTypeType)
              case other => other
            }
            boundary {
              for (((typeParam, variance), typeInSuper) <- supertypeSig.typeParams zip supertypeTypeArgs) {
                val typeInSub = composedSubst.apply(typeParam)
                val typeArgsMatch = variance match {
                  case Variance.Invariant =>
                    val correct = typeInSub == typeInSuper
                    if (!correct) {
                      reportNotSubtype(subT, superT)
                    }
                    correct
                  case Variance.Covariant =>
                    enforceSubtypingConstraintInternal(typeInSub, typeInSuper)
                  case Variance.Contravariant =>
                    enforceSubtypingConstraintInternal(typeInSuper, typeInSub)
                }
                if (!typeArgsMatch) {
                  boundary.break(false)
                }
              }
              true
            }
        }
      case _ =>
        reportNotSubtype(subT, superT)
    }

  }

  extension (subT: BaseType) def trivialSubtypeOf(superT: BaseType)(using program: Program): Boolean = (subT, superT) match {
    case _ if subT == superT => true
    case (NothingType, _) => true
    case (_, VoidType) => false
    case (VoidType, _) => false
    case (_, NothingType) => false
    case (NullType, _) => true
    case (_, NullType) => false
    case (_, AnyType) => true
    case (AnyType, _) => false
    case _ => false
  }

  private def reportNotSubtype(subT: Type, superT: Type)(using errorMsg: ErrorMessage, posOpt: Option[Position], er: ErrorReporter): Boolean = {
    er.push(Err(TypeChecking, errorMsg.msg, posOpt))
    false
  }

  private case class ErrorMessage(msg: String) extends AnyVal

}
