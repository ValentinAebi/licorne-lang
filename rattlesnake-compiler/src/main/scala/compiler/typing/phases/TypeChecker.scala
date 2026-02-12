package compiler.typing.phases

import compiler.identifiers.FunOrVarId
import compiler.lang.Formulas.{Formula, Value}
import compiler.lang.Types.PrimitiveType.UnitType
import compiler.lang.Types.{Type, UnionType}
import compiler.lang.{ClassSignature, RecordSignature, RuntimeTypeSignature, Types}
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.typing.TypeStore
import compiler.typing.smartcasting.ControlFlowInfo

final class TypeChecker(er: ErrorReporter) extends CompilerStep[(Program, TypeStore), (Program, TypeStore)] {

  override def apply(input: (Program, TypeStore)): (Program, TypeStore) = {
    ???
  }
  
  // TODO check that user-provided assignments of type parameters match bounds

  // TODO call for methods and closures
  private def checkReturnsIfNonUnit(retType: Type, endCf: ControlFlowInfo, functionKindDescr: String, posOpt: Option[Position]): Unit = {
    if (retType != UnitType && !endCf.hasExited) {
      reportError(s"missing return in non-$UnitType $functionKindDescr", posOpt)
    }
  }

  private def checkFieldAndReturnType(
                                       ownerVal: Value,
                                       ownerType: Type,
                                       fieldName: FunOrVarId,
                                       posOpt: Option[Position],
                                       checkIsReassignable: Boolean,
                                       ownerThatMustBeThis: Option[Formula]
                                     )(using er: ErrorReporter, program: Program): Option[Type] = {
    program.forceComputeJoins(program.desugarType(ownerType)) match {
      case Some(Types.NamedType(typeName, typeArgs, args)) =>

        def subst(sig: RuntimeTypeSignature, tpe: Type): Type = {
          val subst = sig.typeParams.map(_._1).zip(typeArgs).toMap
          tpe.substitute(subst, Map.empty)
        }

        program.resolveSignatureAs[RuntimeTypeSignature](typeName).flatMap {
          case recordSig: RecordSignature =>
            recordSig.fields.get(fieldName) match {
              case Some(field) => Some(subst(recordSig, field.tpe))
              case None =>
                reportFieldNotFoundInType(ownerType, fieldName, posOpt)
            }
          case classSig: ClassSignature if ownerThatMustBeThis.forall(_ == ownerVal) =>
            classSig.fields.get(fieldName) match {
              case None =>
                reportFieldNotFoundInType(ownerType, fieldName, posOpt)
              case Some(field) =>
                if (checkIsReassignable && field.isStable) {
                  reportError(s"field $fieldName is not reassignable", posOpt)
                }
                Some(subst(classSig, field.tpe))
            }
          case _: ClassSignature =>
            reportError(s"field $fieldName not found or not accessible in $typeName; note that class fields are always private and should be accessed from the outside through getters only", posOpt)
            None
          case _ =>
            reportFieldNotFoundInType(ownerType, fieldName, posOpt)
        }
      case None =>
        val remarkAboutUnion = mkUnionReceiverRemark(ownerType)
        reportError(s"access to field $fieldName: cannot resolve receiver type$remarkAboutUnion", posOpt)
        None
    }
  }

  private def reportFieldNotFoundInType(receiverType: Type, fieldId: FunOrVarId, posOpt: Option[Position])
                                       (using Program): None.type = {
    val receiverTypeDescr = mkReceiverTypeDescr(receiverType)
    reportError(s"field $fieldId not found in $receiverTypeDescr", posOpt)
    None
  }

  private def reportMethodNotFoundInType(receiverType: Type, funId: FunOrVarId, posOpt: Option[Position])(using Program): Unit = {
    val receiverTypeDescr = mkReceiverTypeDescr(receiverType)
    val remarkAboutUnion = mkUnionReceiverRemark(receiverType)
    reportError(s"method $funId not found in $receiverTypeDescr$remarkAboutUnion", posOpt)
  }

  private def mkUnionReceiverRemark(receiverType: Type): String = {
    receiverType match {
      case UnionType(types) => ", you may want to explicitize the type of the receiver using a type ascription"
      case _ => ""
    }
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Warning(TypeChecking, msg, posOpt))
  }
  
  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Err(TypeChecking, msg, posOpt))
  }
  
}
