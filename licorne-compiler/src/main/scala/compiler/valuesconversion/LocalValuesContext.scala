package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, ItId, ThisId}
import compiler.irs.asts.Asts
import compiler.irs.ssa.Formulas.{Formula, IdValue}
import compiler.irs.ssa.SSA.Scope
import compiler.lang.ReassigPermission
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.LocalValuesContext.*
import compiler.valuesconversion.ValuesContext.LocalInfo
import compiler.lang.Types.Type

import scala.annotation.tailrec
import scala.collection.mutable

final class LocalValuesContext(val nestedContext: ValuesContext, val level: Int, val exitManager: ExitManager) extends ValuesContext {

  private val values = mutable.Map.empty[FunOrVarId, LocalInfo]

  export nestedContext.globalCtx
  export globalCtx.resolveObject
  export exitManager.{hasExited, reportHasExitedIfNeeded, markHasExited}
  export exitManager.reset as resetHasExited

  def withOneMoreFrame: LocalValuesContext = new LocalValuesContext(this, level + 1, exitManager.copy)

  override def deepCopyWithSameGlobalCtx: LocalValuesContext = {
    val newExitManager = exitManager.copy
    val copy = new LocalValuesContext(nestedContext.deepCopyWithSameGlobalCtx, level, newExitManager)
    copy.values.addAll(this.values.map((id, info) => (id, info.copy())))
    copy
  }

  def saveNewLocal(id: FunOrVarId, value: Option[IdValue], scope: Scope, reassigPermission: ReassigPermission, declarationTypeAnnot: Option[Type]): Boolean = {
    if (queryLocal(id).isDefined) {
      false
    } else {
      values(id) = LocalInfo(value, scope, reassigPermission, declarationTypeAnnot)
      true
    }
  }

  def saveNewLocal(id: FunOrVarId, value: IdValue, scope: Scope, reassigPermission: ReassigPermission, declarationTypeAnnot: Option[Type]): Boolean =
    saveNewLocal(id, Some(value), scope, reassigPermission, declarationTypeAnnot)

  def remap(id: FunOrVarId, value: IdValue): Boolean = {
    queryLocal(id) match {
      case Some(info) =>
        info.value = Some(value)
        true
      case None => false
    }
  }

  def saveOrRemap(id: FunOrVarId, value: IdValue, scope: Scope, reassigPermission: ReassigPermission, declarationTypeAnnot: Option[Type]): Unit = {
    val saved = saveNewLocal(id, value, scope, reassigPermission, declarationTypeAnnot)
    if (!saved) {
      remap(id, value)
    }
  }
  
  def createShallowCopy(id: FunOrVarId): Boolean = queryLocal(id) match {
    case Some(localInfo) =>
      values(id) = localInfo.copy()
      true
    case None =>
      false
  }

  def valueOf(id: FunOrVarId): ValueQueryResult = queryLocal(id) match {
    case Some(LocalInfo(Some(value), defScope, reassigStatus, declarationTypeAnnot)) =>
      KnownAndInitialized(value, defScope, reassigStatus, declarationTypeAnnot)
    case Some(LocalInfo(None, defScope, reassigStatus, declarationTypeAnnot)) =>
      KnownButUninitialized(id, defScope, reassigStatus, declarationTypeAnnot)
    case None => Unknown(id)
  }

  def getThisValue: Option[IdValue] = valueOf(ThisId).toOption
  
  def getItValue: Option[IdValue] = valueOf(ItId).toOption

  def typeUpperBoundOf(id: FunOrVarId): Option[Type] = queryLocal(id).flatMap(_.declarationTypeAnnot)

  def knows(id: FunOrVarId): Boolean = queryLocal(id).isDefined

  def isReassignableOrUnknown(id: FunOrVarId): Boolean =
    queryLocal(id).forall(_.reassigPermission == ReassigPermission.Var)

  def hasBeenDefinedInCurrentScope(id: FunOrVarId): Boolean = values.contains(id)

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[LocalInfo] = {
    values.get(id) match {
      case someInfo@Some(_) => someInfo
      case None => nestedContext.queryLocal(id)
    }
  }
}

object LocalValuesContext {

  def apply(globalValuesContext: GlobalValuesContext): LocalValuesContext = new LocalValuesContext(globalValuesContext, 0, new ExitManager())

  sealed trait ValueQueryResult {
    def toOption: Option[IdValue] = this match {
      case result: ErrorValueQueryResult => None
      case KnownAndInitialized(value, _, _, _) => Some(value)
    }
  }

  sealed trait ErrorValueQueryResult extends ValueQueryResult

  final case class Unknown(id: FunOrVarId) extends ErrorValueQueryResult

  final case class KnownButUninitialized(id: FunOrVarId, defScope: Scope, reassigStatus: ReassigPermission, declarationTypeAnnotOpt: Option[Type]) extends ErrorValueQueryResult

  final case class KnownAndInitialized(value: IdValue, defScope: Scope, reassigStatus: ReassigPermission, declarationTypeAnnotOpt: Option[Type]) extends ValueQueryResult

  private enum ExitedStatus {
    case Active, HasExited, ReportedHasExited
  }

  final class ExitManager {
    private var exitedStatus = ExitedStatus.Active
    
    def reset(): Unit = {
      exitedStatus = ExitedStatus.Active
    }

    def copy: ExitManager = {
      val copy = new ExitManager()
      copy.exitedStatus = exitedStatus
      copy
    }

    def markHasExited(): Unit = {
      if (exitedStatus == ExitedStatus.Active) {
        exitedStatus = ExitedStatus.HasExited
      }
    }

    def reportHasExitedIfNeeded(er: ErrorReporter, posOpt: Option[Position])
                               (using compilationStep: CompilationStep): Unit = {
      if (exitedStatus == ExitedStatus.HasExited) {
        er.report(Err(compilationStep, "dead code", posOpt))
        exitedStatus = ExitedStatus.ReportedHasExited
      }
    }

    def hasExited: Boolean = exitedStatus != ExitedStatus.Active
  }

}
