package compiler.controlflowchecker

import compiler.analysisctx.AnalysisContext
import compiler.irs.Asts
import compiler.irs.Asts.*
import compiler.pipeline.CompilationStep.PathsChecking
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import lang.CaptureDescriptors.CaptureSet
import lang.Types.PrimitiveTypeShape.{NothingType, VoidType}


final class ControlFlowChecker(er: ErrorReporter) extends CompilerStep[(List[Source], AnalysisContext), (List[Source], AnalysisContext)] {

  override def apply(input: (List[Source], AnalysisContext)): (List[Source], AnalysisContext) = {
    val (sources, analysisContext) = input
    for (src <- sources; df <- src.defs) {
      df match
        case moduleOrPackageDefTree: ModuleOrPackageDefTree =>
          for (fun <- moduleOrPackageDefTree.functions) {
            checkFunction(fun, analysisContext)
          }
        case _: StructDef => ()
        case _: ConstDef => ()
    }
    er.displayAndTerminateIfErrors()
    input
  }

  private def checkFunction(function: FunDef, analysisContext: AnalysisContext): Unit = {
    val ctx = ControlFlowCheckingContext.empty(analysisContext)
    val stateWithParams = function.params.foldLeft(State.initial) { (accState, param) =>
      param.paramNameOpt.map { paramName =>
        ctx.saveLocal(paramName, param.isReassignable, param.tpe.getResolvedType)
        accState.assignmentSaved(paramName)
      }.getOrElse(accState)
    }
    val endState = analyzeStat(stateWithParams, function.body)(using ctx)
    val retType = function.getSignatureOpt.get.retType
    if (!endState.alwaysTerminated && retType != VoidType) {
      er.push(Err(PathsChecking, "missing return in non-Void function", function.getPosition))
    }
    if (retType == NothingType && !endState.alwaysTerminated) {
      er.push(Err(PathsChecking,
        s"cannot prove that function '${function.funName}' with return type '$NothingType' cannot return",
        function.getPosition
      ))
    }
  }

  private def analyzeStat(inState: State, statement: Statement)(using ctx: ControlFlowCheckingContext): State = statement match {
    case expr: Expr => analyzeExpr(inState, expr)
    case Block(stats) =>
      val newCtx = ctx.copyForNarrowedScope()
      var state = inState
      var alreadyReportedDeadCode = false
      for (stat <- stats) {
        alreadyReportedDeadCode |= state.checkIsReachable(er, stat.getPosition)
        state = analyzeStat(state, stat)(using newCtx)
      }
      ctx.unknownVarsRemoved(state)
    case localDef@LocalDef(localName, optTypeAnnot, rhsOpt, isReassignable) =>
      val s = rhsOpt.map(analyzeExpr(inState, _)).getOrElse(inState)
      ctx.saveLocal(localName, isReassignable, localDef.getVarTypeOpt.get)
      s.newLocalSaved(localName, rhsOpt.isDefined)
    case VarAssig(lhs, rhs) =>
      val s1 = stateAfterEvaluatingAssignmentTarget(inState, lhs)
      val s2 = analyzeExpr(s1, rhs)
      checkAssignmentTargetCanStillBeAssigned(lhs, s2)
      markedAssignedIfVariable(lhs, s2)
    case VarModif(lhs, rhs, op) =>
      val s = analyzeExpressions(inState, lhs, rhs)
      checkAssignmentTargetCanStillBeAssigned(lhs, s)
      markedAssignedIfVariable(lhs, s)
    case ite@IfThenElse(cond, thenBr, elseBrOpt) =>
      val stateAfterCond = analyzeExpr(inState, cond)
      val stateAfterThen = analyzeStat(stateAfterCond, thenBr)
      val stateBeforeElse = maybeCaseCoveringCond(cond, stateAfterCond)
      val stateAfterElse = elseBrOpt.map(analyzeStat(stateBeforeElse, _)).getOrElse(stateBeforeElse)
      if (elseBrOpt.isEmpty && stateBeforeElse.isUnfeasible(ctx)){
        ite.markUnfeasibleElse()
        stateAfterThen
      } else {
        stateAfterThen.joined(stateAfterElse)
      }
    case loop@WhileLoop(cond, body) =>
      val stateAfterInitCondEval = analyzeExpr(inState, cond)
      val stateAfterBody = analyzeStat(stateAfterInitCondEval, body)
      if (stateAfterBody.alwaysTerminated) {
        er.push(Warning(PathsChecking, "while does not loop, it should probably be an if", loop.getPosition))
      }
      val stateAfterLoop = stateAfterInitCondEval.joined(stateAfterBody)
      if isTrueLiteral(cond) then stateAfterLoop.terminated() else stateAfterLoop
    case loop@ForLoop(initStats, cond, stepStats, body) =>
      val stateAfterInitStats = analyzeStatements(inState, initStats)
      val stateAfterInitCondEval = analyzeStat(stateAfterInitStats, cond)
      val stateAfterBody = analyzeStat(stateAfterInitCondEval, body)
      if (stateAfterBody.alwaysTerminated) {
        er.push(Warning(PathsChecking, "for does not loop, it should probably be an if", loop.getPosition))
      }
      val stateAfterLoop = stateAfterInitCondEval.joined(stateAfterBody)
      if isTrueLiteral(cond) then stateAfterLoop.terminated() else stateAfterLoop
    case ReturnStat(optVal) =>
      optVal.map(analyzeExpr(inState, _))
        .getOrElse(inState)
        .terminated()
    case PanicStat(msg) =>
      analyzeExpr(inState, msg).terminated()
  }

  private def maybeCaseCoveringCond(cond: Expr, initState: State)
                                   (using ctx: ControlFlowCheckingContext): State = cond match {
    case TypeTest(VariableRef(name), NamedTypeShapeTree(typeName)) if !ctx.isReassignable(name) =>
      initState.handledCaseSaved(name, typeName)
    case _ => initState
  }

  private def analyzeExpr(inState: State, expr: Expr)(using ctx: ControlFlowCheckingContext): State = expr match {
    case literal: Literal => inState
    case varRef: VariableRef =>
      inState.checkIsInitialized(varRef, er)
      inState
    case MeRef() => inState
    case PackageRef(pkgName) => inState
    case DeviceRef(device) => inState
    case call@Call(receiverOpt, function, args, isTailrec) =>
      val preCallState = analyzeExpressions(inState, receiverOpt ++ args)
      if call.getSignatureOpt.get.retType == NothingType
      then preCallState.terminated()
      else preCallState
    case Indexing(indexed, arg) =>
      analyzeExpressions(inState, indexed, arg)
    case ArrayInit(elemType, size) =>
      analyzeExpr(inState, size)
    case FilledArrayInit(arrayElems) =>
      analyzeExpressions(inState, arrayElems)
    case StructOrModuleInstantiation(typeId, args) =>
      analyzeExpressions(inState, args)
    case UnaryOp(operator, operand) =>
      analyzeExpr(inState, operand)
    case BinaryOp(lhs, operator, rhs) =>
      analyzeExpressions(inState, lhs, rhs)
    case Select(lhs, selected) =>
      analyzeExpr(inState, lhs)
    case Ternary(cond, thenBr, elseBr) =>
      val stateAfterCond = analyzeExpr(inState, cond)
      val stateAfterThen = analyzeExpr(stateAfterCond, thenBr)
      val stateAfterElse = analyzeExpr(stateAfterCond, elseBr)
      stateAfterThen.joined(stateAfterElse)
    case Cast(castedExpr, tpe) =>
      analyzeExpr(inState, castedExpr)
    case TypeTest(testedExpr, tpe) =>
      analyzeExpr(inState, testedExpr)
    case Sequence(stats, expr) =>
      val s = analyzeStatements(inState, stats)
      analyzeExpr(s, expr)
  }

  private def analyzeStatements(inState: State, statSeq: Iterable[Statement])(using ControlFlowCheckingContext): State =
    statSeq.foldLeft(inState)(analyzeStat)

  private def analyzeExpressions(inState: State, exprSeq: Iterable[Expr])(using ControlFlowCheckingContext): State =
    exprSeq.foldLeft(inState)(analyzeExpr)

  private def analyzeExpressions(inState: State, exprSeq: Expr*)(using ControlFlowCheckingContext): State =
    exprSeq.foldLeft(inState)(analyzeExpr)

  private def stateAfterEvaluatingAssignmentTarget(inState: State, target: Expr)(using ControlFlowCheckingContext): State = {
    target match {
      case VariableRef(name) => inState
      case Select(lhs, selected) => analyzeExpr(inState, lhs)
      case Indexing(indexed, arg) => analyzeExpressions(inState, indexed, arg)
      case lhs => throw new AssertionError(s"unexpected ${lhs.getClass.getSimpleName} during $PathsChecking")
    }
  }

  private def markedAssignedIfVariable(assignmentTarget: Expr, state: State): State = {
    assignmentTarget match {
      case VariableRef(name) => state.assignmentSaved(name)
      case _ => state
    }
  }

  private def checkAssignmentTargetCanStillBeAssigned(target: Expr, state: State)(using ctx: ControlFlowCheckingContext): Unit = target match {
    case varRef: VariableRef if !ctx.isReassignable(varRef.name) =>
      state.checkIsNotInitialized(varRef, er)
    case _ => ()
  }

  private def isTrueLiteral(expr: Expr): Boolean = {
    expr match
      case BoolLit(true) => true
      case _ => false
  }

}
