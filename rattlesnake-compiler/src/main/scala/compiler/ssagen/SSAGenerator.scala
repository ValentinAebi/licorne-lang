package compiler.ssagen

import compiler.program.Program
import compiler.irs.SSA.*
import compiler.irs.{Asts, SSA}
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext}
import identifiers.*
import lang.*
import lang.Field.{ReassignableField, StableField}
import lang.Types.*
import lang.Values.*

import scala.collection.mutable


final class SSAGenerator(er: ErrorReporter)
  extends CompilerStep[List[Asts.Source], Program] {

  override def apply(input: List[Asts.Source]): Program = {
    val ctxBuilder = Program.Builder(er)
    val globalValuesContext = ctxBuilder.globalValuesContext
    val valuesGen = globalValuesContext.valuesGen
    val allFunctionsCollector = mutable.Map.empty[FunctionSignature, SSA.Function]
    val positionsMapB = Map.newBuilder[TypeIdentifier, Position]
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[Asts.DataTypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        df.getPosition.foreach { pos =>
          positionsMapB.addOne(df.id -> pos)
        }
        val thisValue = valuesGen.newParam(df.id, ConstructorFunId, ThisId)
        df match {
          case df@Asts.InterfaceDef(id, typeParams, functions, directSupertypes) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = true)
            val sig = InterfaceSignature(id, typeParams.convert, funcs, directSupertypes.map(mkNamedType(_, paramsCtx)))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ObjectDef(id, importedObjects, functions, directSupertypes) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val importedObjectsVals = mutable.LinkedHashSet.from(importedObjects.map(globalValuesContext.resolveObject))
            val sig = ObjectSignature(id, importedObjectsVals, funcs, directSupertypes.map(mkNamedType(_, paramsCtx)))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ClassDef(id, typeParams, params, functions, directSupertypes) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val fields = mutable.LinkedHashMap.empty[FunOrVarId, Field]
            val importedObjects = mutable.LinkedHashSet.empty[IdValue]
            params.foreach {
              case Asts.VarParam(paramId, paramTypeTree) =>
                fields(paramId) = ReassignableField(paramId, mkType(paramTypeTree, paramsCtx))
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                val paramType = mkType(paramTypeTree, paramsCtx)
                fields(paramId) = StableField(paramId, paramType, fieldValue)
                paramsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(paramType))
              case Asts.ObjectImport(objectId) =>
                importedObjects.addOne(globalValuesContext.resolveObject(objectId))
            }
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = ClassSignature(id, typeParams.convert, fields, importedObjects, funcs, directSupertypes.map(mkNamedType(_, paramsCtx)))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df: Asts.DataTypeDef =>
            datatypeDefs.addOne(df)
          case Asts.StructDef(id, typeParams, fields, directSupertypes) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            fields.foreach {
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                val fieldType = mkType(paramTypeTree, paramsCtx)
                stableFields(paramId) = StableField(paramId, fieldType, fieldValue)
                paramsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(fieldType))
            }
            val sig = StructSignature(id, typeParams.convert, stableFields, directSupertypes.map(mkNamedType(_, paramsCtx)))
            ctxBuilder.saveSignature(sig, df.getPosition)
            for (superT <- directSupertypes) {
              datatypeSubtypes.getOrElseUpdate(superT.name, mutable.LinkedHashSet.empty).addOne(id)
            }
          case df@Asts.TypeAliasDef(typeName, typeParams, params, rhs) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ItId, thisValue, ReassigPermission.Val, None)
            val typeAliasParams = mutable.LinkedHashMap.empty[FunOrVarId, (Type, IdValue)]
            params.foreach {
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val paramValue = valuesGen.newParam(typeName, ConstructorFunId, paramId)
                val paramType = mkType(paramTypeTree, paramsCtx)
                typeAliasParams(paramId) = (paramType, paramValue)
                paramsCtx.saveNewLocal(paramId, paramValue, ReassigPermission.Val, Some(paramType))
            }
            val sig = TypeAliasSignature(typeName, typeParams.convert, thisValue, typeAliasParams, mkType(rhs, paramsCtx))
            ctxBuilder.saveSignature(sig, df.getPosition)
        }
      }
      for (df@Asts.DataTypeDef(id, typeParams, directSupertypes) <- datatypeDefs) {
        val emptyValsCtx = LocalValuesContext(globalValuesContext)
        val sig = DatatypeSignature(id, typeParams.convert, directSupertypes.map(mkNamedType(_, emptyValsCtx)),
          datatypeSubtypes.getOrElse(id, mutable.LinkedHashSet.empty))
        ctxBuilder.saveSignature(sig, df.getPosition)
      }
    }
    val ctx = ctxBuilder.build(allFunctionsCollector.toMap)
    ctx.checkDefinitions()(using er, positionsMapB.result(), SSAGeneration)
    er.displayAndTerminateIfErrors()
    ctx
  }

  private def collectFunctions(functionsProvider: Asts.EncapsulatedTypeDefTree, globalValsCtx: GlobalValuesContext,
                               allFunctionsCollector: mutable.Map[FunctionSignature, SSA.Function]
                              ): Map[FunOrVarId, (FunctionSignature, Option[SSA.Function])] = {
    val functions = mutable.Map.empty[FunOrVarId, (FunctionSignature, Option[SSA.Function])]
    for (func <- functionsProvider.functions) {
      if (functions.contains(func.id)) {
        reportError(s"a function named ${func.id} has already been declared in ${functionsProvider.description}",
          functionsProvider.getPosition)
      } else {
        val paramsInclThis = mutable.LinkedHashMap.empty[IdValue, Type]
        val thisVal = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, ThisId)
        val funcLocalValsCtx = LocalValuesContext(globalValsCtx)
        val thisParamIsOmitted = func.params.headOption.forall(_.paramId != ThisId)
        val isObject = functionsProvider.isInstanceOf[Asts.ObjectDef]
        if (thisParamIsOmitted && isObject) {
          val thisType = NamedType(functionsProvider.id, List.empty, List.empty, true)
          paramsInclThis(thisVal) = thisType
          funcLocalValsCtx.saveNewLocal(ThisId, thisVal, ReassigPermission.Val, Some(thisType))
        } else if (thisParamIsOmitted && !isObject) {
          reportError(s"parameters list of ${func.id} should start with the receiver parameter (syntax: 'this : Type')", func.getPosition)
        } else if (!thisParamIsOmitted && isObject) {
          warn("receiver parameter can be omitted inside objects", func.getPosition)
        }
        var isFirst = true
        for (paramTree <- func.params) {
          if (paramTree.paramId == ThisId && !isFirst) {
            reportError("receiver parameter should always be at the beginning of the parameters list", func.getPosition)
          } else if (funcLocalValsCtx.knows(paramTree.paramId)) {
            reportError(s"redefinition of parameter ${paramTree.paramId}", paramTree.getPosition)
          } else {
            val paramValue = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, paramTree.paramId)
            val paramType = mkType(paramTree.paramTypeTree, funcLocalValsCtx)
            paramsInclThis(paramValue) = paramType
            funcLocalValsCtx.saveNewLocal(paramTree.paramId, paramValue, ReassigPermission.Val, Some(paramType))
          }
          isFirst = false
        }
        val retType = func.optRetType match {
          case Some(retTypeTree) => mkType(retTypeTree, funcLocalValsCtx)
          case None => PrimitiveType.VoidType
        }
        val sig = FunctionSignature(functionsProvider.id, func.id, func.typeParams, paramsInclThis, retType, func.visibility)
        val bodyOpt = func.bodyOpt.map(generateSSAFunc(sig, _, funcLocalValsCtx, func.getPosition.map(_.srcCodeProviderName)))
        functions(func.id) = (sig, bodyOpt)
        bodyOpt.foreach { body =>
          allFunctionsCollector(sig) = body
        }
      }
    }
    er.displayAndTerminateIfErrors()
    functions.toMap
  }

  private def createIdToSigMapAndCheckBodyExists(functionsMap: Map[FunOrVarId, (FunctionSignature, Option[SSA.Function])],
                                                 funPos: Option[Position], isInterface: Boolean): Map[FunOrVarId, FunctionSignature] = {
    val resultB = Map.newBuilder[FunOrVarId, FunctionSignature]
    for ((id, (sig, optSSA)) <- functionsMap) {
      resultB.addOne(id -> sig)
      if (isInterface && optSSA.isDefined) {
        reportError("methods declared in interfaces are not allowed to have a body", funPos)
      } else if (!isInterface && optSSA.isEmpty) {
        reportError("methods declared in classes and objects must have a body", funPos)
      }
    }
    resultB.result()
  }

  extension (typeParams: List[Asts.TypeParam]) private def convert: List[(TypeIdentifier, Variance)] = typeParams.map {
    case Asts.TypeParam(id, variance) => (id, variance)
  }

  private def generateSSAFunc(sig: FunctionSignature, body: Asts.Block, valsCtx: LocalValuesContext, codeProviderNameOpt: Option[String]): SSA.Function = {
    val ssaInstructionsList = mutable.ListBuffer.empty[SSA.Instr]
    for (stat <- body.stats) {
      generateSSA(stat, valsCtx, ssaInstructionsList)
    }
    SSA.Function(sig, ssaInstructionsList.toList, codeProviderNameOpt)
  }

  private def generateSSA(stat: Asts.Statement, valsCtx: LocalValuesContext, ssaInstructionsList: mutable.ListBuffer[Instr]): Unit = {

    // shadow the name of the outer function so that all recursions go through doGenerateSSA
    val generateSSA: Unit = ()

    def doGenerateSSA(stat: Asts.Statement, valsCtx: LocalValuesContext, ssaInstructionsList: mutable.ListBuffer[SSA.Instr], isRepeat: Boolean): Unit = {
      // @formatter:off
      def reportError(msg: String, posOpt: Option[Position]): Unit = if (!isRepeat) this.reportError(msg, posOpt)
      def warn(msg: String, posOpt: Option[Position]): Unit = if (!isRepeat) this.warn(msg, posOpt)
      // @formatter:on

      if (!isRepeat) {
        valsCtx.reportHasExitedIfNeeded(er, CompilationStep.SSAGeneration, stat.getPosition)
      }
      stat match {
        case expr: Asts.Expr =>
          val convertedExpr = generateSSAExpr(expr, Some(ssaInstructionsList), valsCtx)
          ssaInstructionsList.saveInstr(Evaluate(convertedExpr), stat)
        case Asts.Block(stats) =>
          val blockCtx = valsCtx.withOneMoreFrame
          for (stat <- stats) {
            doGenerateSSA(stat, blockCtx, ssaInstructionsList, isRepeat)
          }
        case localDef@Asts.LocalDef(localName, typeAnnotTreeOpt, rhsOpt, reassigPermission) =>
          val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, valsCtx))
          if (valsCtx.knows(localName)) {
            reportError(s"$localName is already defined in this scope", stat.getPosition)
          } else rhsOpt match {
            case Some(rhs) =>
              doGenerateSSA(localDef.copy(rhsOpt = None).withDesugaringSource(localDef), valsCtx, ssaInstructionsList, isRepeat)
              doGenerateSSA(Asts.VarAssig(
                Asts.VariableRef(localName).withDesugaringSource(localDef),
                None, rhs
              ).withDesugaringSource(localDef), valsCtx, ssaInstructionsList, isRepeat)
            case None =>
              valsCtx.saveNewLocal(localName, None, reassigPermission, typeAnnotOpt)
          }
        case assig@Asts.VarAssig(Asts.VariableRef(lhsLocalId), typeAnnotTreeOpt, rhs) =>
          if (!valsCtx.knows(lhsLocalId)) {
            reportError(s"unknown variable: $lhsLocalId", stat.getPosition)
          }
          if (!valsCtx.isReassignableOrUnknown(lhsLocalId) && valsCtx.valueOf(lhsLocalId).isInstanceOf[KnownAndInitialized]) {
            reportError(s"illegal reassignment of value $lhsLocalId", assig.getPosition)
          }
          val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, valsCtx))
          val rhsFormula = generateSSAExpr(rhs, Some(ssaInstructionsList), valsCtx)
          val newValue = valsCtx.valuesGen.newLocal(lhsLocalId, assig, typeAnnotOpt)
          ssaInstructionsList.saveInstr(Assignment(newValue, rhsFormula), assig)
          valsCtx.remap(lhsLocalId, newValue)
          generateTypeCheckForAnnotIfAny(newValue, typeAnnotOpt, valsCtx, ssaInstructionsList, assig)
        case assig@Asts.VarAssig(indexing@Asts.Indexing(indexedExpr, idxExpr), typeAnnotTreeOpt, rhs) =>
          val indexedValue = generateSSAExprForcedAsVal(indexedExpr, ssaInstructionsList, valsCtx)
          val idxValue = generateSSAExprForcedAsVal(idxExpr, ssaInstructionsList, valsCtx)
          val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, valsCtx))
          val rhsValue = generateSSAExprForcedAsVal(rhs, ssaInstructionsList, valsCtx)
          generateTypeCheckForAnnotIfAny(rhsValue, typeAnnotOpt, valsCtx, ssaInstructionsList, assig)
          ssaInstructionsList.saveInstr(Evaluate(Call(indexedValue, NormalFunOrVarId("set"), List(idxValue, rhsValue))), assig)
        case assig@Asts.VarAssig(Asts.Select(owner, fieldId), typeAnnotTreeOpt, rhs) =>
          val ownerValue = generateSSAExprForcedAsVal(owner, ssaInstructionsList, valsCtx)
          val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, valsCtx))
          val rhsValue = generateSSAExprForcedAsVal(rhs, ssaInstructionsList, valsCtx)
          generateTypeCheckForAnnotIfAny(rhsValue, typeAnnotOpt, valsCtx, ssaInstructionsList, assig)
          ssaInstructionsList.saveInstr(FieldWrite(ownerValue, fieldId, rhsValue), assig)
        case assig@Asts.VarAssig(lhs, typeAnnotOpt, rhs) =>
          reportError("assignment target is not valid", assig.getPosition)
        case Asts.VarModif(lhs@Asts.VariableRef(lhsLocalId), typeAnnot, rhs, op) =>
          doGenerateSSA(
            Asts.VarAssig(
              lhs, typeAnnot,
              Asts.BinaryOp(lhs, op, rhs).withDesugaringSource(stat)
            ).withDesugaringSource(stat),
            valsCtx, ssaInstructionsList, isRepeat
          )
        case Asts.VarModif(lhs, typeAnnot, rhs, op) =>
          reportError("in-place mutation is only allowed on local variables", stat.getPosition)
        case ite@Asts.IfThenElse(cond, thenBr, elseBrOpt) =>
          val condFormula = generateSSAExpr(cond, Some(ssaInstructionsList), valsCtx)
          val thenBrSSA = mutable.ListBuffer.empty[SSA.Instr]
          val thenBrCtx = valsCtx.deepCopyWithSameGlobalCtx
          doGenerateSSA(thenBr, thenBrCtx, thenBrSSA, isRepeat)
          val elseBrSSA = mutable.ListBuffer.empty[SSA.Instr]
          val elseBrCtx = valsCtx.deepCopyWithSameGlobalCtx
          elseBrOpt.foreach { elseBr =>
            doGenerateSSA(elseBr, elseBrCtx, elseBrSSA, isRepeat)
          }
          val phiNodes = valsCtx.unifyAndReturnPhis(ite, thenBrCtx, elseBrCtx)
          ssaInstructionsList.saveInstr(Disjunction(condFormula, thenBrSSA.toList, elseBrSSA.toList, phiNodes), stat)
        case whileLoop@Asts.WhileLoop(cond, body) =>
          val assignedVars = externalVarsAssignedInLoop(whileLoop).toList
          val bodyStartValuesOfModifiedVars = assignedVars.map { varId =>
            varId -> valsCtx.valuesGen.newIntermediate(whileLoop)
          }.toMap
          val loopCtx = valsCtx.deepCopyWithSameGlobalCtx
          for ((id, bodyStartVal) <- bodyStartValuesOfModifiedVars) {
            loopCtx.remap(id, bodyStartVal)
          }
          val condFormula = generateSSAExpr(cond, Some(ssaInstructionsList), loopCtx)
          val bodySSA = mutable.ListBuffer.empty[SSA.Instr]
          doGenerateSSA(body, loopCtx, bodySSA, isRepeat)
          if (loopCtx.exitManager.hasExited) {
            warn("loop body always exits, should be an if statement", whileLoop.getPosition)
            // give up and generate a disjunction instead
            doGenerateSSA(
              Asts.IfThenElse(cond, body, None).withDesugaringSource(whileLoop),
              valsCtx, ssaInstructionsList, isRepeat = true
            )
          } else {
            val preBodyPhisBuilder = List.newBuilder[LoopIterPhi]
            val postLoopPhisBuilder = List.newBuilder[LoopExitPhi]
            for ((id, bodyStartVal) <- bodyStartValuesOfModifiedVars) {
              valsCtx.valueOf(id) match {
                case _: LocalValuesContext.ErrorValueQueryResult => ()
                case LocalValuesContext.KnownAndInitialized(preLoopVal, _, _) =>
                  // if value is known before the loop then it is also after its body
                  val bodyEndVal = loopCtx.valueOf(id).asInstanceOf[KnownAndInitialized].value
                  val postLoopVal = valsCtx.valuesGen.newPhi(id, Set(bodyEndVal), whileLoop.originalAst)
                  if (preLoopVal != bodyEndVal) {
                    preBodyPhisBuilder.addOne(LoopIterPhi(bodyStartVal, preLoopVal, bodyEndVal))
                    postLoopPhisBuilder.addOne(LoopExitPhi(postLoopVal, bodyEndVal, preLoopVal))
                  }
                  val found = valsCtx.remap(id, postLoopVal)
                  assert(found)
              }
            }
            ssaInstructionsList.saveInstr(Loop(preBodyPhisBuilder.result(), condFormula, bodySSA.toList,
              postLoopPhisBuilder.result()), whileLoop)
          }
        case forLoop@Asts.ForLoop(initStats, cond, stepStats, body) =>
          doGenerateSSA(Asts.Block(
            initStats :+ Asts.WhileLoop(cond, Asts.Block(
              body +: stepStats
            ).withDesugaringSource(forLoop)).withDesugaringSource(forLoop)
          ).withDesugaringSource(forLoop), valsCtx, ssaInstructionsList, isRepeat)
        case Asts.ReturnStat(optValExpr) =>
          val optRetVal = optValExpr.map {
            generateSSAExprForcedAsVal(_, ssaInstructionsList, valsCtx)
          }
          ssaInstructionsList.saveInstr(Return(optRetVal), stat)
          valsCtx.markHasExited()
        case panic@Asts.PanicStat(msg) =>
          val msgVal = generateSSAExprForcedAsVal(msg, ssaInstructionsList, valsCtx)
          ssaInstructionsList.saveInstr(Panic(msgVal), panic)
          valsCtx.markHasExited()
      }
    }

    doGenerateSSA(stat, valsCtx, ssaInstructionsList, isRepeat = false)
  }

  private def generateSSAExprForcedAsVal(expr: Asts.Expr, ssaInstructionsList: mutable.ListBuffer[Instr],
                                         valsCtx: LocalValuesContext): Value =
    generateSSAExpr(expr, Some(ssaInstructionsList), valsCtx) match {
      case value: Value => value
      case formula =>
        val resVal = valsCtx.valuesGen.newIntermediate(expr)
        ssaInstructionsList.saveInstr(Assignment(resVal, formula), expr)
        resVal
    }

  private def generateTypeCheckForAnnotIfAny(rhsValue: Value, typeAnnotOpt: Option[Type],
                                             valsCtx: LocalValuesContext, ssaInstructionsList: mutable.ListBuffer[Instr],
                                             astNode: Asts.Ast): Unit = {
    typeAnnotOpt.foreach { typeAnnot =>
      ssaInstructionsList.saveInstr(StaticTypeAssert(rhsValue, typeAnnot), astNode)
    }
  }

  private def generateSSAExpr(expr: Asts.Expr, ssaInstrListOpt: Option[mutable.ListBuffer[SSA.Instr]], valsCtx: LocalValuesContext): Formula = {

    def generateSSAExpr(expr: Asts.Expr): Formula = this.generateSSAExpr(expr, ssaInstrListOpt, valsCtx)

    expr match {
      case Asts.IntLit(value) => IntConstant(value)
      case Asts.DoubleLit(value) => ???
      case Asts.CharLit(value) => ???
      case Asts.BoolLit(true) => True
      case Asts.BoolLit(false) => False
      case Asts.StringLit(value) => StringConstant(value)
      case varRef@Asts.VariableRef(name) =>
        valsCtx.valueOf(name) match {
          case LocalValuesContext.Unknown(id) =>
            reportError(s"not found: $id", varRef.getPosition)
            valsCtx.valuesGen.newMissingValue(name, varRef)
          case LocalValuesContext.KnownButUninitialized(id, reassigStatus, typeUpperBound) =>
            reportError(s"$id might not have been initialized", varRef.getPosition)
            valsCtx.valuesGen.newMissingValue(name, varRef)
          case KnownAndInitialized(value, reassigStatus, typeUpperBound) => value
        }
      case Asts.ThisRef() => generateSSAExpr(Asts.VariableRef(ThisId))
      case Asts.ItRef() => generateSSAExpr(Asts.VariableRef(ItId))
      case Asts.ObjectRef(objectName) => valsCtx.resolveObject(objectName)
      case call@Asts.Call(receiverOpt, funId, args, isTailrec) =>
        val receiver = receiverOpt.map(generateSSAExpr).getOrElse {
          valsCtx.getThisValue match {
            case Some(recv) => recv
            case None =>
              reportError(s"no receiver found for call to $funId", call.getPosition)
              valsCtx.valuesGen.newMissingValue(ThisId, call)
          }
        }
        Call(receiver, funId, args.map(generateSSAExpr))
      case Asts.Indexing(indexed, arg) => Call(generateSSAExpr(indexed), NormalFunOrVarId("get"), List(generateSSAExpr(arg)))
      case Asts.UnaryOp(Operator.Minus, operand) => neg(generateSSAExpr(operand))
      case Asts.UnaryOp(Operator.ExclamationMark, operand) => not(generateSSAExpr(operand))
      case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
      case Asts.BinaryOp(lhs, Operator.Plus, rhs) => plus(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Minus, rhs) => minus(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Times, rhs) => times(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Div, rhs) => div(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Modulo, rhs) => rem(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.GreaterThan, rhs) => lessThan(generateSSAExpr(rhs), generateSSAExpr(lhs))
      case Asts.BinaryOp(lhs, Operator.LessThan, rhs) => lessThan(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.GreaterOrEq, rhs) => lessOrEq(generateSSAExpr(rhs), generateSSAExpr(lhs))
      case Asts.BinaryOp(lhs, Operator.LessOrEq, rhs) => lessOrEq(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Equality, rhs) => equal(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Inequality, rhs) => not(equal(generateSSAExpr(lhs), generateSSAExpr(rhs)))
      case Asts.BinaryOp(lhs, Operator.And, rhs) => and(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Or, rhs) => or(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, operator, rhs) => throw AssertionError(s"unexpected $operator as binary operator")
      case Asts.Select(lhs, selected) => Select(generateSSAExpr(lhs), selected)
      case Asts.TypeTest(expr, tpe) => HasType(generateSSAExpr(expr), mkBasicType(tpe, valsCtx))
      case expr: Asts.NonFormulaExpr => ssaInstrListOpt match {
        case None =>
          reportError("illegal expression: only formulas are allowed in this position", expr.getPosition)
          valsCtx.valuesGen.newIllegalConstruct(expr)
        case Some(ssaInstructionsList) =>
          generateNonFormulaExpr(expr, ssaInstructionsList, valsCtx)
      }
    }
  }

  private def generateNonFormulaExpr(expr: Asts.NonFormulaExpr, ssaInstructionsList: mutable.ListBuffer[SSA.Instr], valsCtx: LocalValuesContext): Formula = expr match {
    case Asts.FilledArrayInit(arrayElems) => ???
    case Asts.StructOrClassInstantiation(typeId, initializers) =>
      val instanceVal = valsCtx.valuesGen.newObject(typeId)
      ssaInstructionsList.saveInstr(Instantiate(instanceVal, typeId), expr)
      initializers.foreach {
        case initializer@Asts.FullFieldInitializer(fieldName, rhs) =>
          ssaInstructionsList.saveInstr(FieldWrite(instanceVal, fieldName, generateSSAExpr(rhs, Some(ssaInstructionsList), valsCtx)), initializer)
        case initializer@Asts.ShorthandFieldInitializer(fieldName) =>
          val rhsExpr = generateSSAExpr(Asts.VariableRef(fieldName).withDesugaringSource(initializer), Some(ssaInstructionsList), valsCtx)
          ssaInstructionsList.saveInstr(FieldWrite(instanceVal, fieldName, rhsExpr), initializer)
      }
      instanceVal
    case ternary@Asts.Ternary(cond, thenBr, elseBr) =>
      val thenResVal = valsCtx.valuesGen.newIntermediate(ternary)
      val elseResVal = valsCtx.valuesGen.newIntermediate(ternary)
      val resultVal = valsCtx.valuesGen.newIntermediate(ternary)
      val condFormula = generateSSAExpr(cond, Some(ssaInstructionsList), valsCtx)
      val thenFormula = generateSSAExpr(thenBr, Some(ssaInstructionsList), valsCtx)
      val elseFormula = generateSSAExpr(elseBr, Some(ssaInstructionsList), valsCtx)
      ssaInstructionsList.saveInstr(Disjunction(condFormula,
        List(Assignment(thenResVal, thenFormula)),
        List(Assignment(elseResVal, elseFormula)),
        List(RegPhi(resultVal, Set(thenResVal, elseResVal)))
      ), ternary)
      elseResVal
    case cast@Asts.Cast(expr, tpe) =>
      val inVal = generateSSAExprForcedAsVal(expr, ssaInstructionsList, valsCtx)
      val resultVal = valsCtx.valuesGen.newIntermediate(cast)
      val targetType = mkBasicType(tpe, valsCtx)
      ssaInstructionsList.saveInstr(Cast(resultVal, inVal, targetType), cast)
      resultVal
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

  private def mkType(typeTree: Asts.TypeTree, valsCtx: LocalValuesContext): Type = typeTree match {
    case Asts.RefinedTypeTree(baseType, predicate) =>
      val baseT = mkBasicType(baseType, valsCtx)
      val refinementCtx = valsCtx.deepCopyWithSameGlobalCtx
      val itVal = valsCtx.valuesGen.newLocal(ItId, typeTree, None)
      refinementCtx.saveOrRemap(ItId, itVal, ReassigPermission.Val, None)
      RefinedType(baseT, itVal, generateSSAExpr(predicate, None, refinementCtx))
    case basicTypeTree: Asts.BaseTypeTree =>
      mkBasicType(basicTypeTree, valsCtx)
  }

  private def mkBasicType(basicTypeTree: Asts.BaseTypeTree, valsCtx: LocalValuesContext): BaseType = basicTypeTree match {
    case Asts.PrimitiveTypeTree(primitiveType) => primitiveType
    case namedTypeTree: Asts.NamedTypeTree => mkNamedType(namedTypeTree, valsCtx)
  }
  
  private def mkNamedType(namedTypeTree: Asts.NamedTypeTree, valsCtx: LocalValuesContext): NamedType = {
    val Asts.NamedTypeTree(name, typeParams, params, isPure) = namedTypeTree
    NamedType(name, typeParams.map(mkType(_, valsCtx)), params.map(generateSSAExpr(_, None, valsCtx)), isPure)
  }

  private def externalVarsAssignedInLoop(loop: Asts.Loop): Set[FunOrVarId] = {
    val assigned = mutable.Set.empty[FunOrVarId]
    val defined = mutable.Set.empty[FunOrVarId]
    loop.preorderWalk {
      case localDef: Asts.LocalDef =>
        defined.addOne(localDef.localName)
      case assignment: Asts.Assignment => assignment.lhs match {
        case Asts.VariableRef(varId) =>
          assigned.addOne(varId)
        case _ => ()
      }
    }
    val assignedVars = assigned.toSet -- defined
    assignedVars
  }

  extension (ssaInstructionsList: mutable.ListBuffer[SSA.Instr]) private def saveInstr(instr: SSA.Instr, node: Asts.Ast): Unit = {
    instr.setAstNode(node.originalAst)
    ssaInstructionsList.addOne(instr)
  }

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.push(Err(SSAGeneration, msg, posOpt))
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.push(Warning(SSAGeneration, msg, posOpt))
  }

}
