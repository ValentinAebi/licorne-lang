package compiler.valuesconversion

import compiler.irs.Asts
import identifiers.{FunOrVarId, NormalFunOrVarId, ThisId}
import lang.CaptureDescriptors.CaptureSet
import lang.{Operator, ReassigPermission}
import lang.Types.{NamedTypeShape, Type, TypeShape}
import lang.Values.{IdValue, *}
import LocalValuesContext.{ErrorsCallbacks, ExitManager, Known, KnownButUninitialized, Unknown, ValueQueryResult}
import compiler.irs.SSA.{Phi, RegPhi}
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.ValuesContext.LocalInfo

import scala.annotation.tailrec
import scala.collection.mutable

final class LocalValuesContext(val nestedContext: ValuesContext, val level: Int, val exitManager: ExitManager) extends ValuesContext {
  nestedContext match {
    case nestedContext: LocalValuesContext => require(!nestedContext.hasExited)
    case _ => ()
  }

  private val regularValues = mutable.Map.empty[FunOrVarId, LocalInfo]

  export nestedContext.{valuesGen, resolveObject, globalCtx}
  export exitManager.{hasExited, reportHasExitedIfNeeded, markHasExited}

  def withOneMoreFrame: LocalValuesContext = new LocalValuesContext(this, level + 1, exitManager)

  override def copyWithSameGlobals: LocalValuesContext = {
    val newExitManager = exitManager.copy
    val copy = new LocalValuesContext(nestedContext.copyWithSameGlobals, level, newExitManager)
    copy.regularValues.addAll(this.regularValues.map((id, info) => (id, info.copy())))
    copy
  }

  def saveNewLocal(id: FunOrVarId, value: Option[Value], reassigStatus: ReassigPermission, typeUpperBound: Option[Type]): Boolean = {
    if (queryLocal(id).isDefined) {
      false
    } else {
      regularValues(id) = LocalInfo(value, reassigStatus, typeUpperBound)
      true
    }
  }

  def saveNewLocal(id: FunOrVarId, value: Value, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]): Boolean =
    saveNewLocal(id, Some(value), reassigStatus, typeUpperBound)

  def saveAssignment(id: FunOrVarId, value: Value): Boolean = {
    queryLocal(id) match {
      case Some(info) =>
        info.value = Some(value)
        true
      case None => false
    }
  }

  def valueOf(id: FunOrVarId): ValueQueryResult = queryLocal(id) match {
    case Some(LocalInfo(Some(value), reassigStatus, typeUpperBound)) => Known(value, reassigStatus, typeUpperBound)
    case Some(LocalInfo(None, reassigStatus, typeUpperBound)) => KnownButUninitialized(id, reassigStatus, typeUpperBound)
    case None => Unknown(id)
  }

  def knows(id: FunOrVarId): Boolean = queryLocal(id).isDefined

  def isReassignable(id: FunOrVarId): Option[Boolean] = queryLocal(id).map(_.reassigStatus == ReassigPermission.Var)

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[LocalInfo] = {
    regularValues.get(id) match {
      case someInfo@Some(_) => someInfo
      case None => nestedContext.queryLocal(id)
    }
  }

  def mkType(typeTree: Asts.TypeTree)(using ErrorsCallbacks): Type = {
    typeTree match {
      case Asts.RefinedTypeTree(baseType, predicate) =>
        val predFormula = mkFormula(predicate)
        mkType(baseType) match {
          case Type(shape, cs, Some(baseRefinement)) => Type(shape, cs, Some(And(baseRefinement, predFormula)))
          case Type(shape, cs, None) => Type(shape, cs, Some(predFormula))
        }
      case Asts.CapturingTypeTree(typeShapeTree, captureDescr) =>
        Type(mkTypeShape(typeShapeTree), mkCapSet(captureDescr), None)
      case typeTree: Asts.TypeShapeTree => mkTypeShape(typeTree).toType
    }
  }

  def mkTypeShape(typeShapeTree: Asts.TypeShapeTree)(using ErrorsCallbacks): TypeShape = typeShapeTree match {
    case Asts.PrimitiveTypeShapeTree(primitiveType) => primitiveType
    case Asts.NamedTypeShapeTree(name, typeParams, params) =>
      NamedTypeShape(name, typeParams.map(mkType), params.map(mkFormula))
  }

  def mkCapSet(captureSetTree: Asts.CaptureSetTree)(using ErrorsCallbacks): CaptureSet = captureSetTree match {
    case Asts.ExplicitCaptureSetTree(capturedExpressions) => ???
    case Asts.ImplicitRootCaptureSetTree() => ???
  }

  def mkFormula(expr: Asts.Expr)(using ErrorsCallbacks): Formula = expr match {
    case expr: Asts.FormulaExpr => mkFormula(expr)
    case _ => valuesGen.newUndefined(expr)
  }

  def mkFormula(expr: Asts.FormulaExpr)(using ErrorsCallbacks): Formula = expr match {
    case Asts.IntLit(value) => IntConstant(value)
    case Asts.DoubleLit(value) => ???
    case Asts.CharLit(value) => ???
    case Asts.BoolLit(true) => True
    case Asts.BoolLit(false) => False
    case Asts.StringLit(value) => StringConstant(value)
    case Asts.VariableRef(name) => valueForLocalRef(name, expr)
    case Asts.ThisRef() => valueForLocalRef(ThisId, expr)
    case Asts.ObjectRef(objectName) => resolveObject(objectName)
    case Asts.Call(receiverOpt, funId, args, isTailrec) =>
      val receiver = receiverOpt.map(mkFormula).getOrElse(queryLocal(ThisId).get.value.get)
      Call(receiver, funId, args.map(mkFormula))
    case Asts.Indexing(indexed, arg) => Call(mkFormula(indexed), NormalFunOrVarId("get"), List(mkFormula(arg)))
    case Asts.UnaryOp(Operator.Minus, operand) => neg(mkFormula(operand))
    case Asts.UnaryOp(Operator.ExclamationMark, operand) => not(mkFormula(operand))
    case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
    case Asts.BinaryOp(lhs, Operator.Plus, rhs) => plus(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Minus, rhs) => minus(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Times, rhs) => times(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Div, rhs) => div(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Modulo, rhs) => rem(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.GreaterThan, rhs) => lessThan(mkFormula(rhs), mkFormula(lhs))
    case Asts.BinaryOp(lhs, Operator.LessThan, rhs) => lessThan(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.GreaterOrEq, rhs) => lessOrEq(mkFormula(rhs), mkFormula(lhs))
    case Asts.BinaryOp(lhs, Operator.LessOrEq, rhs) => lessOrEq(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Equality, rhs) => equal(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Inequality, rhs) => not(equal(mkFormula(lhs), mkFormula(rhs)))
    case Asts.BinaryOp(lhs, Operator.And, rhs) => and(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Or, rhs) => or(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, operator, rhs) => throw AssertionError(s"unexpected $operator as binary operator")
    case Asts.Select(lhs, selected) => Select(mkFormula(lhs), selected)
    case Asts.TypeTest(expr, tpe) => ???
  }

  private def not(operand: Formula): Formula = operand match {
    case True => False
    case False => True
    case _ => Not(operand)
  }

  private def neg(operand: Formula): Formula = operand match {
    case IntConstant(opVal) => IntConstant(-opVal)
    // TODO types other than Int
    case _ => Neg(operand)
  }

  private def plus(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => IntConstant(lv + rv)
    case (l, IntConstant(0)) => l
    case (IntConstant(0), r) => r
    // TODO types other than Int
    case _ => Plus(l, r)
  }

  private def minus(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => IntConstant(lv - rv)
    case (l, IntConstant(0)) => l
    case (IntConstant(0), r) => neg(r)
    // TODO types other than Int
    case _ => Minus(l, r)
  }

  private def times(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => IntConstant(lv * rv)
    // TODO types other than Int
    case _ => Times(l, r)
  }

  private def div(l: Formula, r: Formula): Formula = Div(l, r)

  private def rem(l: Formula, r: Formula): Formula = Rem(l, r)

  private def lessThan(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => if lv < rv then True else False
    // TODO types other than Int
    case _ => LessThan(l, r)
  }

  private def lessOrEq(l: Formula, r: Formula): Formula = (l, r) match {
    case (IntConstant(lv), IntConstant(rv)) => if lv <= rv then True else False
    // TODO types other than Int
    case _ => LessOrEq(l, r)
  }

  private def equal(l: Formula, r: Formula): Formula = (l, r) match {
    case (l: Constant, r: Constant) => if l == r then True else False
    // TODO types other than Int
    case _ => Equal(l, r)
  }

  private def and(l: Formula, r: Formula): Formula = (l, r) match {
    case (True, r) => r
    case (l, True) => l
    case _ => And(l, r)
  }

  private def or(l: Formula, r: Formula): Formula = (l, r) match {
    case (False, r) => r
    case (l, False) => l
    case _ => Or(l, r)
  }

  def unifyAndReturnPhis(children: List[LocalValuesContext]): List[Phi] = {
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
            val newValue = valuesGen.newPhi(inValues)
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
          unify(context.regularValues, inputs.map(_.asInstanceOf[LocalValuesContext].regularValues))
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

  def unifyAndReturnPhis(inputs: LocalValuesContext*): List[Phi] =
    unifyAndReturnPhis(inputs.toList)

  private def valueForLocalRef(name: FunOrVarId, expr: Asts.FormulaExpr)(using errorsCallbacks: ErrorsCallbacks): Value = {
    valueOf(name) match {
      case result: LocalValuesContext.ErrorValueQueryResult =>
        errorsCallbacks.unknownIdCallback(result, expr.getPosition)
        valuesGen.newUndefined(expr)
      case LocalValuesContext.Known(value, reassigStatus, typeUpperBound) => value
    }
  }
}

object LocalValuesContext {

  def apply(globalValuesContext: GlobalValuesContext): LocalValuesContext = new LocalValuesContext(globalValuesContext, 0, new ExitManager())

  final case class ErrorsCallbacks(
                                    unknownIdCallback: (ErrorValueQueryResult, Option[Position]) => Unit,
                                    unexpectedStatCallback: Asts.Statement => Unit
                                  )

  sealed trait ValueQueryResult

  sealed trait ErrorValueQueryResult extends ValueQueryResult

  final case class Unknown(id: FunOrVarId) extends ErrorValueQueryResult

  final case class KnownButUninitialized(id: FunOrVarId, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]) extends ErrorValueQueryResult

  final case class Known(value: Value, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]) extends ValueQueryResult

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
