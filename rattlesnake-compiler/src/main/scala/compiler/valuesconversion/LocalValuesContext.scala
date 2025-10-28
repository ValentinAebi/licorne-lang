package compiler.valuesconversion

import compiler.irs.Asts
import compiler.irs.Asts.{CaptureSetTree, Expr, TypeShapeTree, TypeTree}
import identifiers.FunOrVarId
import lang.CaptureDescriptors.CaptureSet
import lang.Types.{NamedTypeShape, Type, TypeShape}
import lang.Values.*

import scala.collection.mutable

final class LocalValuesContext(val thisValue: Value, val globalCtx: GlobalValuesContext) {
  private val regularValues = mutable.Map.empty[FunOrVarId, Value]
  
  def update(id: FunOrVarId, value: Value): Unit = {
    regularValues(id) = value
  }
  
  def valueOf(id: FunOrVarId): Option[Value] = regularValues.get(id)

  def mkType(typeTree: TypeTree): Type = {
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

  def mkTypeShape(typeShapeTree: TypeShapeTree): TypeShape = typeShapeTree match {
    case Asts.PrimitiveTypeShapeTree(primitiveType) => primitiveType
    case Asts.NamedTypeShapeTree(name, typeParams, params) =>
      NamedTypeShape(name, typeParams.map(mkType), params.map(mkFormula))
  }

  def mkCapSet(captureSetTree: CaptureSetTree): CaptureSet = captureSetTree match {
    case Asts.ExplicitCaptureSetTree(capturedExpressions) => ???
    case Asts.ImplicitRootCaptureSetTree() => ???
  }

  def mkFormula(expr: Expr): Formula = expr match {
    case Asts.IntLit(value) => IntConstant(value)
    case Asts.DoubleLit(value) => ???
    case Asts.CharLit(value) => ???
    case Asts.BoolLit(true) => True
    case Asts.BoolLit(false) => False
    case Asts.StringLit(value) => StringConstant(value)
    case Asts.VariableRef(name) => valueOf(name).getOrElse(globalCtx.valuesGen.newUndefined(expr))
    case Asts.ThisRef() => thisValue
    case Asts.PackageRef(pkgName) => globalCtx.resolvePackage(pkgName)
    case Asts.Call(receiverOpt, funId, args, isTailrec) =>
      Call(receiverOpt.map(mkFormula).getOrElse(thisValue), funId, args.map(mkFormula))
    case Asts.Indexing(indexed, arg) => ???
    case Asts.Select(lhs, selected) => Select(mkFormula(lhs), selected)
    case _ => globalCtx.valuesGen.newUndefined(expr)
  }
  
}
