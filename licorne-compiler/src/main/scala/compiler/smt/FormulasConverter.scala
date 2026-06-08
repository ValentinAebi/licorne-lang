package compiler.smt

import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.{ClosureTypingTarget, FieldResolutionTarget, InvocationTarget}
import compiler.lang.Types
import compiler.lang.Types.PrimitiveType.AnyType
import compiler.smt.FormulasConverter.*
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext
import io.ksmt.KContext
import io.ksmt.expr.KExpr
import io.ksmt.sort.{KBoolSort, KSort, KUninterpretedSort}

import java.util
import scala.util.boundary
import scala.util.boundary.Label

// TODO cache formula conversion
final class FormulasConverter[IntSort <: KSort](
                                                 kCtx: KContext,
                                                 ihm: IntHandlingMode[IntSort],
                                                 dealiasingCtx: DealiasingContext,
                                                 resolCtx: ResolutionContext,
                                                 globalValsContext: GlobalValuesContext,
                                                 proxyStore: ProxyStore,
                                                 counterExBoxOpt: Option[CounterexampleBox]
                                               ) {
  
  private given ResolutionContext = resolCtx
  
  private val anySort = kCtx.mkUninterpretedSort(AnyType.toString)

  private var acceptPhisForInts: Boolean = false

  def acceptingPhisForInts[T](action: => T): T = {
    val preVal = acceptPhisForInts
    acceptPhisForInts = true
    val result = action
    acceptPhisForInts = preVal
    result
  }

  // @formatter:off
  private given KContext = kCtx
  private given DealiasingContext = dealiasingCtx
  // @formatter:on

  def convertInt(formula: Formula): Iterable[KExpr[IntSort]] = savingResult(formula) {
    formula match {
      case value: IdValue =>
        val base = Some(kCtx.mkConst(value.toString, ihm.iSort))
        proxyStore.developDeep(value) match {
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
      // TODO see if *,/,% should be included
      case Times(lhs, rhs) =>
        for {
          l <- convertInt(lhs)
          r <- convertInt(rhs)
        } yield ihm.times(l, r)
      case DivBy(lhs, rhs) =>
        for {
          l <- convertInt(lhs)
          r <- convertInt(rhs)
        } yield ihm.div(l, r)
      case Modulo(lhs, rhs) =>
        for {
          l <- convertInt(lhs)
          r <- convertInt(rhs)
        } yield ihm.modulo(l, r)
      case LogicalNot(operand) => None
      case LogicalAnd(lhs, rhs) => None
      case LogicalOr(lhs, rhs) => None
      case LessOrEq(lhs, rhs) => None
      case LessThan(lhs, rhs) => None
      case Equality(lhs, rhs) => None
      case TypePredicate(subject, tpe) => None
      case Phi(terms) if acceptPhisForInts && terms.nonEmpty =>
        terms.map(convertInt).reduce { (as, bs) =>
          for {
            a <- as
            b <- bs
          } yield {
            val dummyCond = kCtx.mkFreshConst("dummy", kCtx.mkBoolSort())
            kCtx.mkIte(dummyCond, a, b)
          }
        }
      case Phi(terms) => None
    }
  }

  def convertBool(formula: Formula): Iterable[KExpr[KBoolSort]] = savingResult(formula) {
    formula match {
      case value: IdValue =>
        val base = Some(kCtx.mkConst(value.toString, kCtx.mkBoolSort()))
        proxyStore.developDeep(value) match {
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
      case Phi(terms) => None
    }
  }

  def convertObj(formula: Formula): Iterable[KExpr[KUninterpretedSort]] = savingResult(formula) {
    formula match {
      case value: IdValue =>
        val base = Some(kCtx.mkConst(value.toString, anySort))
        proxyStore.developDeep(value) match {
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
  }

  private def mkSelect[S <: KSort](owner: Formula, field: FieldResolutionTarget, sort: S): Iterable[KExpr[S]] = {
    proxyStore.accessorProxyFor(field) match {
      case Some(invkTarget) =>
        mkFunApp(owner, invkTarget, List.empty, sort)
      case None =>
        for {
          ow <- convertObj(owner)
          if field.isResolvedAndStable
        } yield {
          val funDecl = kCtx.mkFuncDecl(selectFuncPrefix + field.fieldId, sort, javaList(anySort))
          kCtx.mkApp(funDecl, javaList(ow))
        }
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
      paramsList.add(paramSort)
      // last should correspond to the proxy
      argsList.add(kArgs.last)
    }
  }

  private def savingResult[S <: KSort](input: Formula)(result: Iterable[KExpr[S]]): Iterable[KExpr[S]] = {
    input match {
      case input: IdValue if input.isInstanceOf[ParamIdValue | ValIdValue | VarIdValue] || input == globalValsContext.itValue =>
        for {
          counterExBox <- counterExBoxOpt
          first <- result.headOption
        } {
          counterExBox.track(input, first)
        }
      case _ => ()
    }
    result
  }

}

object FormulasConverter {

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
