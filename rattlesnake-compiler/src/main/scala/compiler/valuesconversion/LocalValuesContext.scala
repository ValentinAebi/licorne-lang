package compiler.valuesconversion

import compiler.irs.Asts
import compiler.irs.SSA.{Phi, RegPhi}
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.LocalValuesContext.*
import compiler.valuesconversion.ValuesContext.LocalInfo
import identifiers.{FunOrVarId, NormalFunOrVarId, ThisId}
import lang.Types.{NamedType, Type, BasicType}
import lang.Values.*
import lang.{Operator, ReassigPermission}

import scala.annotation.tailrec
import scala.collection.mutable

final class LocalValuesContext(val nestedContext: ValuesContext, val level: Int, val exitManager: ExitManager) extends ValuesContext {
  nestedContext match {
    case nestedContext: LocalValuesContext => require(!nestedContext.hasExited)
    case _ => ()
  }

  private val values = mutable.Map.empty[FunOrVarId, LocalInfo]

  export nestedContext.globalCtx
  export globalCtx.{valuesGen, resolveObject}
  export exitManager.{hasExited, reportHasExitedIfNeeded, markHasExited}

  def withOneMoreFrame: LocalValuesContext = new LocalValuesContext(this, level + 1, exitManager)

  override def copyWithSameGlobals: LocalValuesContext = {
    val newExitManager = exitManager.copy
    val copy = new LocalValuesContext(nestedContext.copyWithSameGlobals, level, newExitManager)
    copy.values.addAll(this.values.map((id, info) => (id, info.copy())))
    copy
  }

  def saveNewLocal(id: FunOrVarId, value: Option[Value], reassigStatus: ReassigPermission, typeUpperBound: Option[Type]): Boolean = {
    if (queryLocal(id).isDefined) {
      false
    } else {
      values(id) = LocalInfo(value, reassigStatus, typeUpperBound)
      true
    }
  }

  def saveNewLocal(id: FunOrVarId, value: Value, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]): Boolean =
    saveNewLocal(id, Some(value), reassigStatus, typeUpperBound)

  def remap(id: FunOrVarId, value: Value): Boolean = {
    queryLocal(id) match {
      case Some(info) =>
        info.value = Some(value)
        true
      case None => false
    }
  }

  def valueOf(id: FunOrVarId): ValueQueryResult = queryLocal(id) match {
    case Some(LocalInfo(Some(value), reassigStatus, typeUpperBound)) =>
      KnownAndInitialized(value, reassigStatus, typeUpperBound)
    case Some(LocalInfo(None, reassigStatus, typeUpperBound)) =>
      KnownButUninitialized(id, reassigStatus, typeUpperBound)
    case None => Unknown(id)
  }
  
  def getThisValue: Option[Value] = valueOf(ThisId) match {
    case result: ErrorValueQueryResult => None
    case KnownAndInitialized(value, reassigStatus, typeUpperBound) => Some(value)
  }

  def typeUpperBoundOf(id: FunOrVarId): Option[Type] = queryLocal(id).flatMap(_.typeUpperBoundOpt)

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

  def unifyAndReturnPhis(ite: Asts.IfThenElse, children: List[LocalValuesContext]): List[Phi] = {
    require(children.forall(_.level == level))

    type Frame = mutable.Map[FunOrVarId, LocalInfo]

    val phiNodesB = List.newBuilder[Phi]

    def unify(result: Frame, inputs: List[Frame]): Unit = {
      for ((id, localInfo) <- result) {
        if (inputs.forall(_.apply(id).value.isDefined)) {
          val inValues = inputs.flatMap(_.apply(id).value).toSet
          if (inValues.size == 1) {
            localInfo.value = Some(inValues.head)
          } else {
            val newValue = valuesGen.newPhi(id, inValues, ite.originalAst)
            phiNodesB.addOne(RegPhi(newValue, inValues))
            localInfo.value = Some(newValue)
          }
        } else {
          assert(localInfo.value.isEmpty)
        }
      }
    }

    @tailrec
    def unifyRecursively(result: ValuesContext, inputs: List[ValuesContext]): Unit = {
      result match {
        case context: LocalValuesContext =>
          unify(context.values, inputs.map(_.asInstanceOf[LocalValuesContext].values))
          unifyRecursively(context.nestedContext, inputs.map(_.asInstanceOf[LocalValuesContext].nestedContext))
        case _ => ()
      }
    }

    val activeChildren = children.filter(!_.hasExited)
    if (activeChildren.forall(_.hasExited)) {
      markHasExited()
    }
    if (activeChildren.isEmpty) {
      List.empty
    } else {
      unifyRecursively(this, activeChildren)
      phiNodesB.result()
    }
  }

  def unifyAndReturnPhis(ite: Asts.IfThenElse, inputs: LocalValuesContext*): List[Phi] =
    unifyAndReturnPhis(ite, inputs.toList)
}

object LocalValuesContext {

  def apply(globalValuesContext: GlobalValuesContext): LocalValuesContext = new LocalValuesContext(globalValuesContext, 0, new ExitManager())

  sealed trait ValueQueryResult

  sealed trait ErrorValueQueryResult extends ValueQueryResult

  final case class Unknown(id: FunOrVarId) extends ErrorValueQueryResult

  final case class KnownButUninitialized(id: FunOrVarId, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]) extends ErrorValueQueryResult

  final case class KnownAndInitialized(value: Value, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]) extends ValueQueryResult

  private enum ExitedStatus {
    case Active, HasExited, ReportedHasExited
  }

  final class ExitManager {
    private var exitedStatus = ExitedStatus.Active

    def copy: ExitManager = {
      val copy = new ExitManager()
      copy.exitedStatus = exitedStatus
      copy
    }

    def markHasExited(): Unit = {
      if (exitedStatus != ExitedStatus.Active) {
        throw IllegalStateException()
      }
      exitedStatus = ExitedStatus.HasExited
    }

    def reportHasExitedIfNeeded(er: ErrorReporter, compilationStep: CompilationStep, posOpt: Option[Position]): Unit = {
      if (exitedStatus == ExitedStatus.HasExited) {
        er.push(Err(compilationStep, "dead code", posOpt))
        exitedStatus = ExitedStatus.ReportedHasExited
      }
    }

    def hasExited: Boolean = exitedStatus != ExitedStatus.Active
  }

}
