package compiler.valuesconversion

import compiler.irs.Asts
import compiler.irs.Asts.{CaptureSetTree, Expr, FormulaExpr, TypeShapeTree, TypeTree}
import identifiers.{FunOrVarId, NormalFunOrVarId, ThisId}
import lang.CaptureDescriptors.CaptureSet
import lang.ReassigPermission.*
import lang.{Operator, ReassigPermission}
import lang.Types.{NamedTypeShape, Type, TypeShape}
import lang.Values.*
import LocalValuesContext.{Known, KnownButUninitialized, Unknown, ErrorsCallbacks, ValueQueryResult}
import compiler.irs.SSA.PhiMerge
import compiler.reporting.Position
import compiler.valuesconversion.ValuesContext.LocalInfo

import scala.annotation.tailrec
import scala.collection.mutable

final class LocalValuesContext(val nestedContext: ValuesContext, val level: Int) extends ValuesContext {
  private val regularValues = mutable.Map.empty[FunOrVarId, LocalInfo]

  export nestedContext.{valuesGen, resolveObject, globalCtx}

  def withOneMoreFrame: LocalValuesContext = new LocalValuesContext(this, level + 1)

  def copyWithOneMoreFrame: LocalValuesContext = copyWithSameGlobal.withOneMoreFrame

  override def copyWithSameGlobal: LocalValuesContext = {
    val copy = new LocalValuesContext(nestedContext.copyWithSameGlobal, level)
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

  def mkType(typeTree: TypeTree)(using ErrorsCallbacks): Type = {
    typeTree match {
      case Asts.RefinedTypeTree(baseType, predicate) =>
        val predFormula = mkFormula(predicate)
        mkType(baseType) match {
          case Type(shape, cs, Some(baseRefinement)) => Type(shape, cs, Some(And(baseRefinement, predFormula)))
          case Type(shape, cs, None) => Type(shape, cs, Some(predFormula))
        }
      case Asts.CapturingTypeTree(typeShapeTree, captureDescr) =>
        Type(mkTypeShape(typeShapeTree), mkCapSet(captureDescr), None)
      case typeTree: TypeShapeTree => mkTypeShape(typeTree).toType
    }
  }

  def mkTypeShape(typeShapeTree: TypeShapeTree)(using ErrorsCallbacks): TypeShape = typeShapeTree match {
    case Asts.PrimitiveTypeShapeTree(primitiveType) => primitiveType
    case Asts.NamedTypeShapeTree(name, typeParams, params) =>
      NamedTypeShape(name, typeParams.map(mkType), params.map(mkFormula))
  }

  def mkCapSet(captureSetTree: CaptureSetTree)(using ErrorsCallbacks): CaptureSet = captureSetTree match {
    case Asts.ExplicitCaptureSetTree(capturedExpressions) => ???
    case Asts.ImplicitRootCaptureSetTree() => ???
  }

  def mkFormula(expr: Expr)(using ErrorsCallbacks): Formula = expr match {
    case expr: FormulaExpr => mkFormula(expr)
    case _ => valuesGen.newUndefined(expr)
  }

  def mkFormula(expr: FormulaExpr)(using ErrorsCallbacks): Formula = expr match {
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
    case Asts.UnaryOp(Operator.Minus, operand) => Neg(mkFormula(operand))
    case Asts.UnaryOp(Operator.ExclamationMark, operand) => Not(mkFormula(operand))
    case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
    case Asts.BinaryOp(lhs, Operator.Plus, rhs) => Plus(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Minus, rhs) => Minus(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Times, rhs) => Times(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Div, rhs) => Div(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Modulo, rhs) => Rem(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.GreaterThan, rhs) => LessThan(mkFormula(rhs), mkFormula(lhs))
    case Asts.BinaryOp(lhs, Operator.LessThan, rhs) => LessThan(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.GreaterOrEq, rhs) => LessOrEq(mkFormula(rhs), mkFormula(lhs))
    case Asts.BinaryOp(lhs, Operator.LessOrEq, rhs) => LessOrEq(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Equality, rhs) => Equal(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Inequality, rhs) => Not(Equal(mkFormula(lhs), mkFormula(rhs)))
    case Asts.BinaryOp(lhs, Operator.And, rhs) => And(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, Operator.Or, rhs) => Or(mkFormula(lhs), mkFormula(rhs))
    case Asts.BinaryOp(lhs, operator, rhs) => throw AssertionError(s"unexpected $operator as binary operator")
    case Asts.Select(lhs, selected) => Select(mkFormula(lhs), selected)
    case Asts.TypeTest(expr, tpe) => ???
  }

  private def valueForLocalRef(name: FunOrVarId, expr: FormulaExpr)(using errorsCallbacks: ErrorsCallbacks): Value = {
    valueOf(name) match {
      case result: LocalValuesContext.ErrorValueQueryResult =>
        errorsCallbacks.unknownIdCallback(result, expr.getPosition)
        valuesGen.newUndefined(expr)
      case LocalValuesContext.Known(value, reassigStatus, typeUpperBound) => value
    }
  }
}

object LocalValuesContext {
  
  def apply(globalValuesContext: GlobalValuesContext): LocalValuesContext = new LocalValuesContext(globalValuesContext, 0)

  def unificationCodeFor(commonAncestor: LocalValuesContext, children: List[LocalValuesContext]): List[PhiMerge] = {
    require(children.nonEmpty)
    
    type Frame = mutable.Map[FunOrVarId, LocalInfo]

    val valuesGen = commonAncestor.valuesGen
    val phiNodesB = List.newBuilder[PhiMerge]

    def unify(result: Frame, inputs: List[Frame]): Unit = {
      for ((id, localInfo) <- result) {
        if (inputs.forall(_.apply(id).value.isDefined)) {
          val inValues = inputs.flatMap(_.apply(id).value).toSet
          if (inValues.size == 1) {
            localInfo.value = Some(inValues.head)
          } else {
            val newValue = valuesGen.newPhi(inValues)
            phiNodesB.addOne(PhiMerge(newValue, inValues))
            localInfo.value = Some(newValue)
          }
        } else {
          assert(localInfo.value.isEmpty)
        }
      }
    }
    
    @tailrec
    def dropNestedFrames(inputs: List[LocalValuesContext], result: LocalValuesContext): List[LocalValuesContext] = {
      val inputsAfter = inputs.map(in => if in.level > result.level then in.nestedContext.asInstanceOf[LocalValuesContext] else in)
      if inputsAfter == inputs then inputsAfter else dropNestedFrames(inputsAfter, result)
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
    
    unifyRecursively(commonAncestor, dropNestedFrames(children, commonAncestor))
    phiNodesB.result()
  }

  def unificationCodeFor(commonAncestor: LocalValuesContext, children: LocalValuesContext*): List[PhiMerge] =
    unificationCodeFor(commonAncestor, children.toList)

  final case class ErrorsCallbacks(
                                    unknownIdCallback: (ErrorValueQueryResult, Option[Position]) => Unit,
                                    unexpectedStatCallback: Asts.Statement => Unit
                                  )

  sealed trait ValueQueryResult

  sealed trait ErrorValueQueryResult extends ValueQueryResult

  final case class Unknown(id: FunOrVarId) extends ErrorValueQueryResult

  final case class KnownButUninitialized(id: FunOrVarId, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]) extends ErrorValueQueryResult

  final case class Known(value: Value, reassigStatus: ReassigPermission, typeUpperBound: Option[Type]) extends ValueQueryResult

}
