package compiler.typechecking

import compiler.pipeline.CompilationStep.TypeChecking
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.util.zipCommons
import lang.Formulas.Formula
import lang.Types.*
import lang.Types.PrimitiveType.*
import lang.{RuntimeTypeSignature, TypeTypeParamInfo, Variance}
import solver.Solver

import scala.util.boundary

// TODO also pass the subject (formula whose type is being asserted) to the subtype checking methods, to be used by the SMT solver
object SubtypeRelation {

  def enforceExpectedSubtypingConstraint(subT: Type, superT: Type, positionDescr: String)
                                        (using posOpt: Option[Position], er: ErrorReporter, solver: Solver, program: Program): Boolean = {
    checkSubtypingConstraint(subT, superT)(using Reporting(er, s"$positionDescr: expected ${superT.withTypeVarsExpanded}, found ${subT.withTypeVarsExpanded}", posOpt))
  }

  def enforceSubtypingConstraintCustomMsg(subT: Type, superT: Type, fullMsg: String)
                                         (using posOpt: Option[Position], er: ErrorReporter, solver: Solver, program: Program): Boolean = {
    checkSubtypingConstraint(subT, superT)(using Reporting(er, fullMsg, posOpt))
  }

  private def checkSubtypingConstraint(subT: Type, superT: Type)
                                      (using reporting: Reporting, solver: Solver, program: Program): Boolean = {
    (program.desugarType(subT), program.desugarType(superT)) match {
      case (subT: TypeVariable, superT) =>
        subT.resolve(superT)
        checkAssignmentIsValid(subT, superT)
        true
      case (subT, superT: TypeVariable) =>
        superT.resolve(subT)
        checkAssignmentIsValid(superT, subT)
        true
      case (subT, superT) =>
        checkSubtypingConstraintOnDesugaredTypes(subT, superT)
    }
  }

  private def checkSubtypingConstraintOnDesugaredTypes(subT: Type, superT: Type)
                                                      (using reporting: Reporting, solver: Solver, program: Program): Boolean = {
    (subT, superT) match {
      case (subT, superT) if subT.trivialSubtypeOf(superT) => true
      case (NamedType(subtypeName, subtypeTypeArgs, subtypeArgs), NamedType(supertypeName, supertypeTypeArgs, supertypeArgs)) =>
        assert(subtypeArgs.isEmpty)
        assert(supertypeArgs.isEmpty)
        program.subToSuperSubst(subtypeName, supertypeName) match {
          case None =>
            reportNotSubtype(subT, superT)
            false
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
              for ((TypeTypeParamInfo(typeParam, variance, _, _), typeInSuper) <- supertypeSig.typeParams zip supertypeTypeArgs) {
                val typeInSub = composedSubst.apply(typeParam)
                val typeArgsMatch = variance match {
                  case Variance.Invariant =>
                    checkSubtypingConstraint(typeInSub, typeInSuper) && checkSubtypingConstraint(typeInSuper, typeInSub)
                  case Variance.Covariant =>
                    checkSubtypingConstraint(typeInSub, typeInSuper)
                  case Variance.Contravariant =>
                    checkSubtypingConstraint(typeInSuper, typeInSub)
                }
                if (!typeArgsMatch) {
                  boundary.break(false)
                }
              }
              true
            }
        }
      case (subT: IntRangeType, superT: IntRangeType) =>
        solver.canProveIntRangeSubtyping(subT, superT)
      case (ClosureType(subParams, subResult), ClosureType(superParams, superResult)) =>
        val sizeMatch = subParams.size == superParams.size
        if (!sizeMatch) {
          reportNotSubtype(subT, superT)
        }
        val argsMatch = subParams.zipCommons(superParams).forall { (subParamType, superParamType) =>
          checkSubtypingConstraint(superParamType, subParamType)
        }
        val retMatch = checkSubtypingConstraint(subResult, superResult)
        sizeMatch && argsMatch && retMatch
      case (UnionType(subtypes), superT) =>
        val subtypesIter = subtypes.iterator
        var isCorrect = true
        while (isCorrect && subtypesIter.hasNext) {
          isCorrect = checkSubtypingConstraint(subtypesIter.next(), superT)
        }
        isCorrect
      case (subT, UnionType(superTypes)) =>
        superTypes.exists(checkSubtypingConstraint(subT, _))
      case _ =>
        reportNotSubtype(subT, superT)
        false
    }

  }

  extension (subT: Type) def trivialSubtypeOf(superT: Type)(using program: Program): Boolean = (subT.principalType, superT) match {
    case (subT, superT) if subT == superT => true
    case (NothingType, _) => true
    case (_, UnitType) => true
    case (_, NothingType) => false
    case (NullType, _) => true
    case (_, NullType) => false
    case (_, AnyType) => true
    case (AnyType, _) => false
    case _ => false
  }

  private def checkAssignmentIsValid(tv: TypeVariable, tpe: Type)(using solver: Solver, program: Program, reporting: Reporting): Boolean = {
    given Reporting = reporting.copy(msg = s"type variable $tv has been assigned to type $tpe, which violates its bounds")

    tv.upperBoundOpt.forall(checkSubtypingConstraint(tpe, _)) && tv.lowerBoundOpt.forall(checkSubtypingConstraint(_, tpe))
  }

  private def reportNotSubtype(subT: Type, superT: Type)(using reporting: Reporting): Unit = {
    val Reporting(er, msg, posOpt) = reporting
    er.report(Err(TypeChecking, msg, posOpt))
  }

  private case class Reporting(er: ErrorReporter, msg: String, posOpt: Option[Position])

}
