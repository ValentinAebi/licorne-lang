package compiler.smt

import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.{ClosureTypingTarget, FieldResolutionTarget, Formulas, InvocationTarget}
import compiler.lang.Types
import compiler.lang.Types.IntRangeType
import compiler.lang.Types.PrimitiveType.AnyType
import compiler.smt.Z3Solver.{closureInvkFunId, javaList, selectFuncPrefix}
import compiler.typing.contexts.DealiasingContext
import compiler.valproxies.ProxyStore
import io.ksmt.KContext
import io.ksmt.expr.KExpr
import io.ksmt.solver.KSolverStatus
import io.ksmt.solver.z3.KZ3Solver
import io.ksmt.sort.{KBoolSort, KSort, KUninterpretedSort}

import java.util
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.util.boundary
import scala.util.boundary.Label


// TODO cache formula conversion
final class Z3Solver[IntSort <: KSort] private[smt](kCtx: KContext, kZ3Solver: KZ3Solver, ihm: IntHandlingMode[IntSort], dealiasingCtx: DealiasingContext, proxyStore: ProxyStore) extends Solver {
  private val anySort = kCtx.mkUninterpretedSort(AnyType.toString)

  private given KContext = kCtx

  // useful for debugging
  private val assertionsStack = mutable.Stack(mutable.LinkedHashSet.empty[KExpr[KBoolSort]])

  private given DealiasingContext = dealiasingCtx

  def check(): KSolverStatus = kZ3Solver.check()

  def checkSat(): Boolean = check() == KSolverStatus.SAT

  def checkUnsat(): Boolean = check() == KSolverStatus.UNSAT

  def canProve(formula: Formula): Boolean = onNewFrame {
    assert(LogicalNot(formula))
    checkUnsat()
  }

  def canProveImplication(premise: Formula, conseq: Formula): Boolean = onNewFrame {
    assert(premise)
    assert(LogicalNot(conseq))
    checkUnsat()
  }

  def canProveLeq(lhs: Formula, rhs: Formula): Boolean = onNewFrame {
    assertLt(rhs, lhs)
    checkUnsat()
  }

  def canProveLt(lhs: Formula, rhs: Formula): Boolean = onNewFrame {
    assertLeq(rhs, lhs)
    checkUnsat()
  }

  def canProveGeZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(IntConst(0), f)
  }

  def canProveGtZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(IntConst(1), f)
  }

  def canProveLeZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(f, IntConst(0))
  }

  def canProveLtZero(f: Option[Formula]): Boolean = f.exists { f =>
    canProveLeq(f, IntConst(-1))
  }

  def canProveNotZero(f: Formula): Boolean = {
    canProve(LogicalNot(Equality(f, IntConst(0))))
  }

  def onNewFrame[T](action: => T): T = {
    assertionsStack.push(mutable.LinkedHashSet.empty)
    kZ3Solver.push()
    val res = try {
      action
    } finally {
      kZ3Solver.pop()
      assertionsStack.pop()
    }
    res
  }

  def intMin(l: Formula, r: Formula): Option[Formula] = {
    if canProveLeq(l, r) then Some(l)
    else if canProveLeq(r, l) then Some(r)
    else None
  }

  def intMin(formulas: Iterable[Formula]): Option[Formula] = findMinOrMax(formulas, intMin)

  def intMax(l: Formula, r: Formula): Option[Formula] = {
    if canProveLeq(l, r) then Some(r)
    else if canProveLeq(r, l) then Some(l)
    else None
  }

  def intMax(formulas: Iterable[Formula]): Option[Formula] = findMinOrMax(formulas, intMax)

  private def findMinOrMax(formulas: Iterable[Formula], minOrMaxFunc: (Formula, Formula) => Option[Formula]): Option[Formula] =
    if formulas.isEmpty then None
    else {
      val iter = formulas.iterator
      var minOrMax = iter.next()
      while (iter.hasNext) {
        minOrMaxFunc(minOrMax, iter.next()) match {
          case Some(newMinOrMax) =>
            minOrMax = newMinOrMax
          case None =>
            return None
        }
      }
      Some(minOrMax)
    }

  def assert(formula: Formula): Unit = {
    for {
      kFormula <- convertBool(formula)
    } {
      doAssert(kFormula)
    }
  }

  def assert(formulas: Iterable[Formula]): Unit = {
    for {
      formula <- formulas
      kFormula <- convertBool(formula)
    } {
      doAssert(kFormula)
    }
  }

  def assertEq[S <: KSort](lhs: Formula, rhs: Formula, simplifiedType: SimplifiedType[S]): Unit = {
    val conversionFunc: Formula => Iterable[KExpr[S]] = (simplifiedType: @unchecked) match {
      case SimplifiedType.Integer[IntSort] () => convertInt
      case SimplifiedType.Boolean => convertBool
      case SimplifiedType.Object => convertObj
    }
    for {
      l <- conversionFunc(lhs)
      r <- conversionFunc(rhs)
    } do {
      doAssert(kCtx.eq(l, r))
    }
  }

  def assertLeq(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertInt(lhs)
      r <- convertInt(rhs)
    } do {
      doAssert(ihm.leq(l, r))
    }
  }

  def assertLt(lhs: Formula, rhs: Formula): Unit = {
    for {
      l <- convertInt(lhs)
      r <- convertInt(rhs)
    } do {
      doAssert(ihm.lt(l, r))
    }
  }

  def assertInRange(formula: Formula, range: IntRangeType): Unit = {
    range.lowerBoundOpt.foreach { lb =>
      assertLeq(lb, formula)
    }
    range.upperBoundOpt.foreach { ub =>
      assertLeq(formula, ub)
    }
  }

  def canProveIsOutsideRange(formula: Formula, range: IntRangeType): Boolean = onNewFrame {
    range.lowerBoundOpt.exists { lb =>
      canProveLt(formula, lb)
    } || range.upperBoundOpt.exists { ub =>
      canProveLt(ub, formula)
    }
  }

  private def convertInt(formula: Formula): Iterable[KExpr[IntSort]] = formula match {
    case value: IdValue =>
      val base = Some(kCtx.mkConst(value.toString, ihm.iSort))
      proxyStore.getProxy(value) match {
        case Some(proxy) if proxy != value && proxy.isPure =>
          base ++ convertInt(proxy)
        case _ => base
      }
    case IntConst(value) => Some(ihm.const(value))
    case BoolConst(value) => None
    case StringConst(value) => None
    case Select(owner, field) if field.isResolvedAndStable =>
      mkSelect(owner, field, ihm.iSort)
    case Select(owner, field) => None
    case FunCall(receiver, func, typeArgs, args) if func.isResolvedAndPure =>
      mkFunApp(receiver, func, args, ihm.iSort)
    case FunCall(receiver, func, typeArgs, args) => None
    case ClosureCall(callee, closureTypingTarget, args) if closureTypingTarget.isResolvedAndPure =>
      mkClosureApp(callee, closureTypingTarget, args, ihm.iSort)
    case ClosureCall(callee, closureTypingTarget, args) => None
    case PureClosureValue(params, body, closureVal) => None
    case Plus(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield ihm.plus(l, r)
    case Neg(negated) =>
      for {
        n <- convertInt(negated)
      } yield ihm.neg(n)
    case Times(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield ihm.times(l, r) // TODO see if we keep or not, as it introduces indecidability
    case DivBy(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield ihm.div(l, r) // TODO see if division and modulo should be included
    case Modulo(lhs, rhs) => None
    case LogicalNot(operand) => None
    case LogicalAnd(lhs, rhs) => None
    case LogicalOr(lhs, rhs) => None
    case LessOrEq(lhs, rhs) => None
    case LessThan(lhs, rhs) => None
    case Equality(lhs, rhs) => None
    case TypePredicate(subject, tpe) => None
  }

  private def convertBool(formula: Formula): Iterable[KExpr[KBoolSort]] = formula match {
    case value: IdValue =>
      val base = Some(kCtx.mkConst(value.toString, kCtx.mkBoolSort()))
      proxyStore.getProxy(value) match {
        case Some(proxy) if proxy != value && proxy.isPure =>
          base ++ convertBool(proxy)
        case _ => base
      }
    case IntConst(value) => None
    case BoolConst(value) => Some(kCtx.mkBool(value))
    case StringConst(value) => None
    // TODO encode selects
    case Select(owner, field) if field.isResolvedAndStable =>
      mkSelect(owner, field, kCtx.mkBoolSort())
    case Select(owner, field) => None
    case FunCall(receiver, func, typeArgs, args) if func.isResolvedAndPure =>
      mkFunApp(receiver, func, args, kCtx.mkBoolSort())
    case FunCall(receiver, func, typeArgs, args) => None
    case ClosureCall(callee, closureTypingTarget, args) if closureTypingTarget.isResolvedAndPure =>
      mkClosureApp(callee, closureTypingTarget, args, kCtx.mkBoolSort())
    case ClosureCall(callee, closureTypingTarget, args) => None
    case PureClosureValue(params, body, closureVal) => None
    case Plus(lhs, rhs) => None
    case Neg(operand) => None
    case Times(lhs, rhs) => None
    case DivBy(lhs, rhs) => None
    case Modulo(lhs, rhs) => None
    case LogicalNot(operand) =>
      for {
        kOperand <- convertBool(operand)
      } yield kCtx.mkNot(kOperand)
    case LogicalAnd(lhs, rhs) =>
      for {
        l <- convertBool(lhs)
        r <- convertBool(rhs)
      } yield kCtx.mkAnd(l, r)
    case LogicalOr(lhs, rhs) =>
      for {
        l <- convertBool(lhs)
        r <- convertBool(rhs)
      } yield kCtx.mkOr(l, r)
    case LessOrEq(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield ihm.leq(l, r)
    case LessThan(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield ihm.lt(l, r)
    case Equality(lhs, rhs) =>
      for {
        l <- convertInt(lhs)
        r <- convertInt(rhs)
      } yield kCtx.mkEq(l, r)
    case TypePredicate(subject, tpe) => None
  }

  private def convertObj(formula: Formula): Iterable[KExpr[KUninterpretedSort]] = formula match {
    case value: IdValue =>
      val base = Some(kCtx.mkConst(value.toString, anySort))
      proxyStore.getProxy(value) match {
        case Some(proxy) if proxy != value && proxy.isPure =>
          base ++ convertObj(proxy)
        case _ => base
      }
    case formula: ConstFormula => None
    case Select(owner, field) if field.isResolvedAndStable =>
      mkSelect(owner, field, anySort)
    case FunCall(receiver, func, typeArgs, args) if func.isResolvedAndPure =>
      mkFunApp(receiver, func, args, anySort)
    case ClosureCall(callee, closureTypingTarget, args) if closureTypingTarget.isResolvedAndPure =>
      mkClosureApp(callee, closureTypingTarget, args, anySort)
    case PureClosureValue(params, body, closureVal) => None
    case _ => None
  }

  private def mkSelect[S <: KSort](owner: Formula, field: FieldResolutionTarget, sort: S): Iterable[KExpr[S]] = {
    for {
      ow <- convertObj(owner)
      if field.isResolvedAndStable
    } yield {
      val funDecl = kCtx.mkFuncDecl(selectFuncPrefix + field.fieldId, sort, javaList(anySort))
      kCtx.mkApp(funDecl, javaList(ow))
    }
  }

  private def mkFunApp[S <: KSort](receiver: Formula, func: InvocationTarget, args: List[Formula], sort: S): Iterable[KExpr[S]] = boundary {
    val funSig = func.getFunSigUnsafe
    for {
      rec <- convertObj(receiver)
      if func.isResolvedAndPure && funSig.paramsWithoutThis.size == args.size
    } yield {
      val paramsList = new util.ArrayList[KSort]()
      val argsList = new util.ArrayList[KExpr[?]]()
      paramsList.add(anySort)
      argsList.add(rec)
      processArguments(funSig.paramsWithoutThis.map(_._2), args, paramsList, argsList)
      val decl = kCtx.mkFuncDecl(funSig.smtFunctionCode, sort, paramsList)
      kCtx.mkApp(decl, argsList)
    }
  }

  private def mkClosureApp[S <: KSort](callee: Formula, closureTypingTarget: ClosureTypingTarget, args: List[Formula], sort: S): Iterable[KExpr[S]] = boundary {
    for {
      cal <- convertObj(callee)
      if closureTypingTarget.isResolvedAndPure
    } yield {
      val paramsList = new util.ArrayList[KSort]()
      val argsList = new util.ArrayList[KExpr[?]]()
      paramsList.add(anySort)
      argsList.add(cal)
      processArguments(closureTypingTarget.getTypeUnsafe.params, args, paramsList, argsList)
      val decl = kCtx.mkFuncDecl(closureInvkFunId, sort, paramsList)
      kCtx.mkApp(decl, argsList)
    }
  }

  private def processArguments[S <: KSort](params: Iterable[Types.Type], args: List[Formula],
                                           paramsList: util.ArrayList[KSort], argsList: util.ArrayList[KExpr[?]])
                                          (using Label[Iterable[KExpr[S]]]): Unit = {
    for ((paramType, arg) <- params zip args) {
      val (paramSort, kArgs) = SimplifiedType.from(paramType) match {
        case SimplifiedType.Integer() => ihm.iSort -> convertInt(arg)
        case SimplifiedType.Boolean => kCtx.mkBoolSort() -> convertBool(arg)
        case SimplifiedType.Object => anySort -> convertObj(arg)
      }
      if (kArgs.isEmpty) {
        boundary.break(Seq.empty)
      }
      for (kArg <- kArgs) {
        paramsList.add(paramSort)
        argsList.add(kArg)
      }
    }
  }

  private def doAssert[S <: KSort](kFormula: KExpr[KBoolSort]) = {
    kZ3Solver.assert(kFormula)
    assertionsStack.head.addOne(kFormula)
  }

}

object Z3Solver {

  private val selectFuncPrefix: String = "select$fld$"
  private val closureInvkFunId = "closure$invk"

  private def javaList[T](elems: T*): java.util.List[T] = {
    val ls = new java.util.ArrayList[T](elems.size)
    for (elem <- elems) {
      ls.add(elem)
    }
    ls
  }

}
