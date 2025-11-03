package compiler.valuesconversion

import compiler.irs.Asts
import compiler.irs.Asts.{CaptureSetTree, Expr, FormulaExpr, TypeShapeTree, TypeTree}
import identifiers.{FunOrVarId, NormalFunOrVarId, ThisId}
import lang.CaptureDescriptors.CaptureSet
import lang.ReassigStatus.*
import lang.{Operator, ReassigStatus}
import lang.Types.{NamedTypeShape, Type, TypeShape}
import lang.Values.*
import LocalValuesContext.{Known, KnownButUninitialized, Unknown, UnknownIdCallback, ValueQueryResult}
import compiler.irs.SSA.PhiMerge
import compiler.reporting.Position
import compiler.valuesconversion.ValuesContext.LocalInfo

import scala.collection.mutable

final class LocalValuesContext(val nestedContext: ValuesContext) extends ValuesContext {

  private val regularValues = mutable.Map.empty[FunOrVarId, LocalInfo]

  export nestedContext.{valuesGen, resolveObject}

  def withOneMoreLayer: LocalValuesContext = LocalValuesContext(this)

  // TODO user-facing methods

  override private[valuesconversion] def updateLocal(id: FunOrVarId, value: Value): Boolean = {
    regularValues.get(id) match {
      case Some(info) =>
        info.value = value
        true
      case None =>
        nestedContext.updateLocal(id, value)
    }
  }

  override private[valuesconversion] def queryLocal(id: FunOrVarId): Option[LocalInfo] = {
    regularValues.get(id) match {
      case someInfo@Some(_) => someInfo
      case None => nestedContext.queryLocal(id)
    }
  }

  def mkType(typeTree: TypeTree)(using unknownIdCallback: UnknownIdCallback): Type = {
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

  def mkTypeShape(typeShapeTree: TypeShapeTree)(using unknownIdCallback: UnknownIdCallback): TypeShape = typeShapeTree match {
    case Asts.PrimitiveTypeShapeTree(primitiveType) => primitiveType
    case Asts.NamedTypeShapeTree(name, typeParams, params) =>
      NamedTypeShape(name, typeParams.map(mkType), params.map(mkFormula))
  }

  def mkCapSet(captureSetTree: CaptureSetTree)(using unknownIdCallback: UnknownIdCallback): CaptureSet = captureSetTree match {
    case Asts.ExplicitCaptureSetTree(capturedExpressions) => ???
    case Asts.ImplicitRootCaptureSetTree() => ???
  }

  def mkFormula(expr: Expr)(using unknownIdCallback: UnknownIdCallback): Formula = expr match {
    case expr: FormulaExpr => mkFormula(expr)
    case _ => globalCtx.valuesGen.newUndefined(expr)
  }

  def mkFormula(expr: FormulaExpr)(using unknownIdCallback: UnknownIdCallback): Formula = expr match {
    case Asts.IntLit(value) => IntConstant(value)
    case Asts.DoubleLit(value) => ???
    case Asts.CharLit(value) => ???
    case Asts.BoolLit(true) => True
    case Asts.BoolLit(false) => False
    case Asts.StringLit(value) => StringConstant(value)
    case Asts.VariableRef(name) => valueOf(name) match {
      case result: LocalValuesContext.ErrorValueQueryResult =>
        unknownIdCallback(result, expr.getPosition)
        valuesGen.newUndefined(expr)
      case LocalValuesContext.Known(value, reassigStatus, typeUpperBound) => value
    }
    case Asts.ThisRef() => thisValue
    case Asts.ObjectRef(objectName) => globalCtx.resolveObject(objectName)
    case Asts.Call(receiverOpt, funId, args, isTailrec) =>
      Call(receiverOpt.map(mkFormula).getOrElse(thisValue), funId, args.map(mkFormula))
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
  }

}

object LocalValuesContext {

  def mergeCodeFor(commonAncestorCtx: LocalValuesContext, leftCtx: LocalValuesContext, rightCtx: LocalValuesContext): List[PhiMerge] = {
    val lsB = List.newBuilder[PhiMerge]
    for (id <- commonAncestorCtx.regularValues.keys){
      val LocalInfo(vl, rsl, tubl) = leftCtx.regularValues.apply(id)
      val LocalInfo(vr, rsr, tubr) = rightCtx.regularValues.apply(id)
      assert(rsl == rsr)
      assert(tubl == tubr)
      (vl, vr) match {
        case (Some(vl), Some(vr)) =>
          if (vl != vr){
            val inputs = List(vl, vr)
            val outVal = commonAncestorCtx.valuesGen.newPhi(inputs)
            lsB.addOne(PhiMerge(outVal, inputs))
          }
        case _ => ()
      }
    }
    lsB.result()
  }
  
  final case class UnknownIdCallback(callback: (ErrorValueQueryResult, Option[Position]) => Unit) extends AnyVal {
    export callback.apply
  }

  sealed trait ValueQueryResult
  sealed trait ErrorValueQueryResult extends ValueQueryResult
  final case class Unknown(id: FunOrVarId) extends ErrorValueQueryResult
  final case class KnownButUninitialized(id: FunOrVarId, reassigStatus: ReassigStatus, typeUpperBound: Option[Type]) extends ErrorValueQueryResult
  final case class Known(value: Value, reassigStatus: ReassigStatus, typeUpperBound: Option[Type]) extends ValueQueryResult
  
}
