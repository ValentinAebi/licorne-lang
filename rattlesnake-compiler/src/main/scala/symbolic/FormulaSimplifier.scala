package symbolic

import lang.Values
import lang.Values.{Formula, IdValue}
import org.matheclipse.core.eval.ExprEvaluator
import org.matheclipse.core.expression.{F, IntegerSym, S}
import org.matheclipse.core.interfaces.{IExpr, ISymbol}

import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable

final class FormulaSimplifier {
  private val symbols = mutable.Map.empty[IdValue, ISymbol]
  private val uidGenerator = AtomicInteger(0)

  def formulaToStringSimplified(formula: Formula): String = {
    val evaluator = ExprEvaluator()
    val expr = convertToIExpr(formula)
    evaluator.eval(expr).toString
  }

  private def convertToIExpr(formula: Formula): IExpr = formula match {
    case value: IdValue => symbolFor(value)
    case Values.True => S.True
    case Values.False => S.False
    case Values.NullPtr => S.Null
    case Values.UnitVal => S.Null // TODO see if this representation is correct
    case Values.IntConstant(value) => IntegerSym(value)
    case Values.DoubleConstant(value) => ???
    case Values.StringConstant(value) => ???
    case Values.Plus(lhs, rhs) => F.Plus(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.Minus(lhs, rhs) => F.Subtract(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.Times(lhs, rhs) => F.Times(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.Div(lhs, rhs) => F.Divide(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.Rem(lhs, rhs) => F.Mod(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.And(lhs, rhs) => F.And(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.Or(lhs, rhs) => F.Or(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.LessThan(lhs, rhs) => F.Less(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.LessOrEq(lhs, rhs) => F.LessEqual(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.Equal(lhs, rhs) => F.Equal(convertToIExpr(lhs), convertToIExpr(rhs))
    case Values.Neg(operand) => F.Negate(convertToIExpr(operand))
    case Values.Not(operand) => F.Not(convertToIExpr(operand))
    case Values.Call(receiver, funId, typeArgs, args) =>
      val typeArgsStr = if typeArgs.isEmpty then "" else typeArgs.mkString("[", ",", "]")
      val argsStr = args.mkString("(", ",", ")")
      genPlaceholderFor(s"${convertToIExpr(receiver)}.$funId$typeArgsStr$argsStr")
    case Values.ClosureInvocation(closure, args) =>
      genPlaceholderFor(s"${convertToIExpr(closure)}${args.mkString("(", ",", ")")}")
    case Values.Select(owner, fieldName) =>
      genPlaceholderFor(s"${convertToIExpr(owner)}.$fieldName")
    case Values.HasType(formula, tpe) =>
      genPlaceholderFor(s"${convertToIExpr(formula)} is $tpe")
  }

  private def genPlaceholderFor(formulaStr: String) =
    F.Dummy(uidGenerator.incrementAndGet().toString)

  private def symbolFor(idValue: IdValue): ISymbol = symbols.getOrElseUpdate(idValue, {
    F.Dummy(idValue.completeDescr)
  })

}
