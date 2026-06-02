package compiler.valuesconversion

import compiler.identifiers.{FunOrVarId, ItId, ThisId}
import compiler.irs.asts.Asts
import compiler.irs.ssa.Formulas.{Formula, IdValue}
import compiler.irs.ssa.SSA.{LocalDecl, Scope}
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

  {
    // FIXME check this
    values.put(ItId, LocalInfo(Some(globalCtx.itValue), globalCtx.globalScope, ReassigPermission.Val, None))
  }

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
    case Some(localInfo@LocalInfo(Some(value), defScope, reassigStatus, declarationTypeAnnot)) =>
      KnownAndInitialized(localInfo)
    case Some(localInfo@LocalInfo(None, defScope, reassigStatus, declarationTypeAnnot)) =>
      KnownButUninitialized(id, localInfo)
    case None => Unknown(id)
  }

  def getThisValue: Option[IdValue] = valueOf(ThisId).toOption

  def getItValue: Option[IdValue] = valueOf(ItId).toOption

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
      case KnownAndInitialized(value, _, _, _) => Some(value)
      case _ => None
    }

    def declOpt: Option[LocalDecl] = this match {
      case found: KnownAndInitialized => found.localInfo.declaration
      case found: KnownButUninitialized => found.localInfo.declaration
      case _ => None
    }
    
    def setDecl(localDecl: LocalDecl): Unit = this match {
      case found: KnownAndInitialized =>
        found.localInfo.declaration = localDecl
      case found: KnownButUninitialized =>
        found.localInfo.declaration = localDecl
      case _ => ()
    }

  }

  sealed trait ErrorValueQueryResult extends ValueQueryResult

  final case class Unknown(id: FunOrVarId) extends ErrorValueQueryResult

  final class KnownButUninitialized(val id: FunOrVarId, val localInfo: LocalInfo) extends ErrorValueQueryResult {
    require(localInfo.value.isEmpty)
    export localInfo.{defScope, reassigPermission, declarationTypeAnnotOpt}
  }

  object KnownButUninitialized {
    def unapply(vqr: ValueQueryResult): Option[(FunOrVarId, Scope, ReassigPermission, Option[Type])] = vqr match {
      case vqr: KnownButUninitialized =>
        val LocalInfo(_, defScope, reassigPermission, declarationTypeAnnot) = vqr.localInfo
        Some(vqr.id, defScope, reassigPermission, declarationTypeAnnot)
      case _ => None
    }
  }

  final class KnownAndInitialized(val localInfo: LocalInfo) extends ValueQueryResult {
    require(localInfo.value.isDefined)

    def value: IdValue = localInfo.value.get

    export localInfo.{defScope, reassigPermission, declarationTypeAnnotOpt}
  }

  object KnownAndInitialized {
    def unapply(vqr: ValueQueryResult): Option[(IdValue, Scope, ReassigPermission, Option[Type])] = vqr match {
      case vqr: KnownAndInitialized =>
        val LocalInfo(valueOpt, defScope, reassigPermission, declarationTypeAnnot) = vqr.localInfo
        Some(valueOpt.get, defScope, reassigPermission, declarationTypeAnnot)
      case _ => None
    }
  }

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
