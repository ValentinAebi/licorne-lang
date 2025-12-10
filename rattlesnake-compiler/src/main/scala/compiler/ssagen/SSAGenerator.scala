package compiler.ssagen

import compiler.irs.Asts.{NamedTypeTree, VarParam}
import compiler.irs.SSA.*
import compiler.irs.{Asts, SSA}
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext}
import identifiers.*
import lang.*
import lang.Field.{ReassignableField, StableField}
import lang.Types.*
import lang.Values.*

import java.util
import scala.collection.{SeqMap, mutable}
import scala.collection.mutable.ListBuffer


final class SSAGenerator(er: ErrorReporter)
  extends CompilerStep[List[Asts.Source], Program] {

  override def apply(input: List[Asts.Source]): Program = {
    given formulaPositions: util.IdentityHashMap[Formula, Position] = util.IdentityHashMap()

    val ctxBuilder = Program.Builder(er)
    val globalValuesContext = ctxBuilder.globalValuesContext
    val valuesGen = globalValuesContext.valuesGen
    val allFunctionsCollector = mutable.SeqMap.empty[FunctionSignature, SSA.Function]
    val positionsMapB = Map.newBuilder[TypeIdentifier, Position]
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[Asts.DataTypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        df.getPosition.foreach { pos =>
          positionsMapB.addOne(df.id -> pos)
        }
        val thisValue = valuesGen.newValue(ThisId)
        df match {
          case df@Asts.InterfaceDef(id, typeParams, functions, directSupertypes) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val noFunctionsSig = InterfaceSignature(id, typeParams.convert, Map.empty, directSupertypes.map(mkNamedType(_, paramsCtx)))
            val functionsMap = collectFunctions(df, noFunctionsSig, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = true)
            val sig = noFunctionsSig.copy(functions = funcs)
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ObjectDef(id, importedObjects, functions, directSupertypes) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val importedObjectsVals = mutable.LinkedHashSet.from(importedObjects.map(globalValuesContext.resolveObject))
            val noFunctionsSig = ObjectSignature(id, importedObjectsVals, Map.empty, directSupertypes.map(mkNamedType(_, paramsCtx)))
            val functionsMap = collectFunctions(df, noFunctionsSig, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
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
                val fieldValue = valuesGen.newValue(id)
                val paramType = mkType(paramTypeTree, paramsCtx)
                fields(paramId) = StableField(paramId, paramType, fieldValue)
                paramsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(paramType))
              case Asts.ObjectImport(objectId) =>
                importedObjects.addOne(globalValuesContext.resolveObject(objectId))
            }
            val noFunctionsSig = ClassSignature(id, typeParams.convert, fields, importedObjects, Map.empty, directSupertypes.map(mkNamedType(_, paramsCtx)))
            val functionsMap = collectFunctions(df, noFunctionsSig, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df: Asts.DataTypeDef =>
            datatypeDefs.addOne(df)
          case Asts.RecordDef(id, typeParams, fields, directSupertypes) =>
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            fields.foreach {
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newValue(paramId)
                val fieldType = mkType(paramTypeTree, paramsCtx)
                stableFields(paramId) = StableField(paramId, fieldType, fieldValue)
                paramsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(fieldType))
            }
            val sig = RecordSignature(id, typeParams.convert, stableFields, directSupertypes.map(mkNamedType(_, paramsCtx)))
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
                val paramValue = valuesGen.newValue(paramId)
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
    val ctx = ctxBuilder.build(allFunctionsCollector, formulaPositions)
    ctx.checkDefinitions()(using er, positionsMapB.result(), SSAGeneration)
    er.displayAndTerminateIfErrors()
    ctx
  }

  private def collectFunctions(
                                functionsProvider: Asts.EncapsulatedTypeDefTree,
                                functionsProviderIncompleteSig: Encapsulated,
                                globalValsCtx: GlobalValuesContext,
                                allFunctionsCollector: mutable.Map[FunctionSignature, SSA.Function]
                              )(using util.IdentityHashMap[Formula, Position]): SeqMap[FunOrVarId, (FunctionSignature, SSA.Function)] = {
    val functions = mutable.LinkedHashMap.empty[FunOrVarId, (FunctionSignature, SSA.Function)]
    for (func <- functionsProvider.functions) {
      if (functions.contains(func.id)) {
        reportError(s"a function named ${func.id} has already been declared in ${functionsProvider.description}", func.getPosition)
      } else {
        val paramsInclThis = mutable.LinkedHashMap.empty[IdValue, Type]
        val thisVal = functionsProvider match {
          case Asts.ObjectDef(id, importedObjects, functions, directSupertypes) => globalValsCtx.resolveObject(id)
          case _ => globalValsCtx.valuesGen.newValue(ThisId)
        }
        val funcLocalValsCtx = LocalValuesContext(globalValsCtx)
        val thisParamIsOmitted = func.params.headOption.forall(_.paramId != ThisId)
        val isObject = functionsProvider.isInstanceOf[Asts.ObjectDef]
        if (thisParamIsOmitted && isObject) {
          val thisType = NamedType(functionsProvider.id, List.empty, List.empty)
          paramsInclThis(thisVal) = thisType
          funcLocalValsCtx.saveNewLocal(ThisId, thisVal, ReassigPermission.Val, Some(thisType))
        } else if (thisParamIsOmitted && !isObject) {
          reportError(s"parameters list of ${func.id} should start with the receiver parameter (syntax: 'this : Type')", func.getPosition)
        } else if (!thisParamIsOmitted && isObject) {
          warn("receiver parameter can be omitted inside objects", func.getPosition)
        }
        var isFirst = true
        for (paramTree <- func.params) {
          if (funcLocalValsCtx.knows(paramTree.paramId)) {
            reportError(s"redefinition of parameter ${paramTree.paramId}", paramTree.getPosition)
          } else {
            val paramValue = globalValsCtx.valuesGen.newValue(paramTree.paramId)
            val paramType = paramTree match {
              case Asts.ThisParam(paramTypeTreeOpt) =>
                if (!isFirst) {
                  reportError("receiver parameter should always be at the beginning of the parameters list", func.getPosition)
                }
                val expectedThisType = functionsProviderIncompleteSig.toType(Map.empty, Map.empty)
                paramTypeTreeOpt.map { paramTypeTree =>
                  val actualThisType = mkType(paramTypeTree, funcLocalValsCtx)
                  if (actualThisType.baseType != expectedThisType) {
                    reportError(s"unexpected type for receiver parameter; expected was $expectedThisType (not that it may be omitted)", func.getPosition)
                  }
                  actualThisType
                }.getOrElse(expectedThisType)
              case paramTree: Asts.NonThisFunctionParam =>
                mkType(paramTree.paramTypeTree, funcLocalValsCtx)
            }
            paramsInclThis(paramValue) = paramType
            val reassigPermission = if paramTree.isInstanceOf[VarParam] then ReassigPermission.Var else ReassigPermission.Val
            funcLocalValsCtx.saveNewLocal(paramTree.paramId, paramValue, reassigPermission, Some(paramType))
          }
          isFirst = false
        }
        val retType = func.optRetType match {
          case Some(retTypeTree) => mkType(retTypeTree, funcLocalValsCtx)
          case None => PrimitiveType.VoidType
        }
        val sig = FunctionSignature(functionsProvider.id, func.id, func.typeParams, paramsInclThis, retType, func.visibility)
        val bodyOpt = generateSSAFunc(sig, func.bodyOpt, funcLocalValsCtx, func.getPosition)
        functions(func.id) = (sig, bodyOpt)
        allFunctionsCollector(sig) = bodyOpt
      }
    }
    er.displayAndTerminateIfErrors()
    functions
  }

  private def createIdToSigMapAndCheckBodyExists(functionsMap: SeqMap[FunOrVarId, (FunctionSignature, SSA.Function)],
                                                 funPos: Option[Position], isInterface: Boolean): Map[FunOrVarId, FunctionSignature] = {
    val resultB = Map.newBuilder[FunOrVarId, FunctionSignature]
    for ((id, (sig, optSSA)) <- functionsMap) {
      resultB.addOne(id -> sig)
      if (isInterface && optSSA.bodyOpt.isDefined) {
        reportError("methods declared in interfaces are not allowed to have a body", funPos)
      } else if (!isInterface && optSSA.bodyOpt.isEmpty) {
        reportError("methods declared in classes and objects must have a body", funPos)
      }
    }
    resultB.result()
  }

  extension (typeParams: List[Asts.TypeParam]) private def convert: List[(TypeIdentifier, Variance)] = typeParams.map {
    case Asts.TypeParam(id, variance) => (id, variance)
  }

  private def generateSSAFunc(
                               sig: FunctionSignature,
                               bodyOpt: Option[Asts.Block],
                               valsCtx: LocalValuesContext,
                               posOpt: Option[Position]
                             )(using util.IdentityHashMap[Formula, Position]): SSA.Function = bodyOpt match {
    case Some(body) =>
      val ssaInstructionsList = mutable.ListBuffer.empty[SSA.Instr]
      for (stat <- body.stats) {
        generateSSA(stat, valsCtx, ssaInstructionsList)
      }
      SSA.Function(sig, Some(ssaInstructionsList.toList), posOpt)
    case None =>
      SSA.Function(sig, None, posOpt)
  }

  private def generateSSA(
                           stat: Asts.Statement,
                           valsCtx: LocalValuesContext,
                           ssaInstructionsList: mutable.ListBuffer[Instr]
                         )(using util.IdentityHashMap[Formula, Position]): Unit = {

    def generateSSA(stat: Asts.Statement, valsCtx: LocalValuesContext, ssaInstructionsList: mutable.ListBuffer[SSA.Instr], isRepeat: Boolean): Unit = {
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
            generateSSA(stat, blockCtx, ssaInstructionsList, isRepeat)
          }
        case localDef@Asts.LocalDef(localName, typeAnnotTreeOpt, rhsOpt, reassigPermission) =>
          val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, valsCtx))
          if (valsCtx.knows(localName)) {
            reportError(s"$localName is already defined in this scope", stat.getPosition)
          } else rhsOpt match {
            case Some(rhs) =>
              generateSSA(localDef.copy(rhsOpt = None).withDesugaringSource(localDef), valsCtx, ssaInstructionsList, isRepeat)
              generateSSA(Asts.VarAssig(Asts.VariableRef(localName).withDesugaringSource(localDef), rhs)
                .withDesugaringSource(localDef), valsCtx, ssaInstructionsList, isRepeat)
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
          val newValue = valsCtx.valuesGen.newValue(lhsLocalId)
          ssaInstructionsList.saveInstr(Assignment(newValue, rhsFormula), assig)
          valsCtx.remap(lhsLocalId, newValue)
          generateTypeCheckForAnnotIfAny(newValue, typeAnnotOpt, valsCtx, ssaInstructionsList, assig)
        case assig@Asts.VarAssig(Asts.Select(owner, fieldId), typeAnnotTreeOpt, rhs) =>
          val ownerValue = generateSSAExprForcedAsVal(owner, ssaInstructionsList, valsCtx)
          val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, valsCtx))
          val rhsValue = generateSSAExprForcedAsVal(rhs, ssaInstructionsList, valsCtx)
          generateTypeCheckForAnnotIfAny(rhsValue, typeAnnotOpt, valsCtx, ssaInstructionsList, assig)
          ssaInstructionsList.saveInstr(FieldWrite(ownerValue, fieldId, rhsValue), assig)
        case assig@Asts.VarAssig(lhs, typeAnnotOpt, rhs) =>
          reportError("assignment target is not valid", assig.getPosition)
        case Asts.VarModif(lhs@Asts.VariableRef(lhsLocalId), typeAnnot, rhs, op) =>
          generateSSA(
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
          generateSSA(thenBr, thenBrCtx, thenBrSSA, isRepeat)
          val elseBrSSA = mutable.ListBuffer.empty[SSA.Instr]
          val elseBrCtx = valsCtx.deepCopyWithSameGlobalCtx
          elseBrOpt.foreach { elseBr =>
            generateSSA(elseBr, elseBrCtx, elseBrSSA, isRepeat)
          }
          val phiNodes = valsCtx.unifyAndReturnPhis(ite, thenBrCtx, elseBrCtx)
          ssaInstructionsList.saveInstr(Disjunction(condFormula, thenBrSSA.toList, elseBrSSA.toList, phiNodes), stat)
        case whileLoop@Asts.WhileLoop(cond, body) =>
          val assignedVars = externalVarsAssignedInLoop(whileLoop).toList
          val bodyStartValuesOfModifiedVars = assignedVars.map { varId =>
            varId -> valsCtx.valuesGen.newValue(varId)
          }.toMap
          val loopCtx = valsCtx.deepCopyWithSameGlobalCtx
          for ((id, bodyStartVal) <- bodyStartValuesOfModifiedVars) {
            loopCtx.remap(id, bodyStartVal)
          }
          val condFormula = generateSSAExpr(cond, Some(ssaInstructionsList), loopCtx)
          val bodySSA = mutable.ListBuffer.empty[SSA.Instr]
          generateSSA(body, loopCtx, bodySSA, isRepeat)
          if (loopCtx.exitManager.hasExited) {
            warn("loop body always exits, should be an if statement", whileLoop.getPosition)
            // give up and generate a disjunction instead
            generateSSA(
              Asts.IfThenElse(cond, body, None).withDesugaringSource(whileLoop),
              valsCtx, ssaInstructionsList, isRepeat = true
            )
          } else {
            val loopVars = List.newBuilder[LoopVarInfo]
            for ((id, bodyStartVal) <- bodyStartValuesOfModifiedVars) {
              valsCtx.valueOf(id) match {
                case _: LocalValuesContext.ErrorValueQueryResult => ()
                case LocalValuesContext.KnownAndInitialized(preLoopVal, _, _) =>
                  // if value is known before the loop then it is also known after its body
                  val bodyEndVal = loopCtx.valueOf(id).asInstanceOf[KnownAndInitialized].value
                  val postLoopVal = valsCtx.valuesGen.newValue(id)
                  if (preLoopVal != bodyEndVal) {
                    loopVars.addOne(LoopVarInfo(id, preLoopVal, bodyStartVal, bodyEndVal, postLoopVal))
                  }
                  val found = valsCtx.remap(id, postLoopVal)
                  assert(found)
              }
            }
            ssaInstructionsList.saveInstr(Loop(condFormula, bodySSA.toList, loopVars.result()), whileLoop)
          }
        case forLoop@Asts.ForLoop(initStats, cond, stepStats, body) =>
          generateSSA(Asts.Block(
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

    generateSSA(stat, valsCtx, ssaInstructionsList, isRepeat = false)
  }

  private def generateSSAExprForcedAsVal(
                                          expr: Asts.Expr,
                                          ssaInstructionsList: mutable.ListBuffer[Instr],
                                          valsCtx: LocalValuesContext
                                        )(using util.IdentityHashMap[Formula, Position]): IdValue =
    generateSSAExpr(expr, Some(ssaInstructionsList), valsCtx) match {
      case value: IdValue => value
      case formula =>
        val resVal = valsCtx.valuesGen.newValue()
        ssaInstructionsList.saveInstr(Assignment(resVal, formula), expr)
        resVal
    }

  private def generateTypeCheckForAnnotIfAny(
                                              rhsValue: Value,
                                              typeAnnotOpt: Option[Type],
                                              valsCtx: LocalValuesContext,
                                              ssaInstructionsList: mutable.ListBuffer[Instr],
                                              astNode: Asts.Ast
                                            ): Unit = {
    typeAnnotOpt.foreach { typeAnnot =>
      ssaInstructionsList.saveInstr(StaticTypeAssert(rhsValue, typeAnnot), astNode)
    }
  }

  private def generateSSAExpr(
                               expr: Asts.Expr,
                               ssaInstrListOpt: Option[mutable.ListBuffer[SSA.Instr]],
                               valsCtx: LocalValuesContext
                             )(using formulaPositions: util.IdentityHashMap[Formula, Position]): Formula = {

    def generateSSAExpr(expr: Asts.Expr): Formula = this.generateSSAExpr(expr, ssaInstrListOpt, valsCtx)

    val formula = expr match {
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
            valsCtx.valuesGen.newValue(name)
          case LocalValuesContext.KnownButUninitialized(id, reassigStatus, typeUpperBound) =>
            reportError(s"$id might not have been initialized", varRef.getPosition)
            valsCtx.valuesGen.newValue(name)
          case KnownAndInitialized(value, reassigStatus, typeUpperBound) => value
        }
      case Asts.ThisRef() => generateSSAExpr(Asts.VariableRef(ThisId))
      case Asts.ItRef() => generateSSAExpr(Asts.VariableRef(ItId))
      case Asts.ObjectRef(objectName) => valsCtx.resolveObject(objectName)
      case call@Asts.Call(receiverOpt, funId, typeArgs, args) =>
        val receiver = receiverOpt.map(generateSSAExpr).getOrElse {
          valsCtx.getThisValue match {
            case Some(recv) => recv
            case None =>
              reportError(s"no receiver found for call to $funId", call.getPosition)
              valsCtx.valuesGen.newValue(ThisId)
          }
        }
        Call(receiver, funId, typeArgs.map(mkType(_, valsCtx)), args.map(generateSSAExpr))
      case Asts.UnaryOp(Operator.Minus, operand) => Neg(generateSSAExpr(operand))
      case Asts.UnaryOp(Operator.ExclamationMark, operand) => Not(generateSSAExpr(operand))
      case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
      case Asts.BinaryOp(lhs, Operator.Plus, rhs) => Plus(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Minus, rhs) => Minus(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Times, rhs) => Times(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Div, rhs) => Div(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Modulo, rhs) => Rem(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.GreaterThan, rhs) => LessThan(generateSSAExpr(rhs), generateSSAExpr(lhs))
      case Asts.BinaryOp(lhs, Operator.LessThan, rhs) => LessThan(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.GreaterOrEq, rhs) => LessOrEq(generateSSAExpr(rhs), generateSSAExpr(lhs))
      case Asts.BinaryOp(lhs, Operator.LessOrEq, rhs) => LessOrEq(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Equality, rhs) => Equal(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Inequality, rhs) => Not(Equal(generateSSAExpr(lhs), generateSSAExpr(rhs)))
      case Asts.BinaryOp(lhs, Operator.And, rhs) => And(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, Operator.Or, rhs) => Or(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case Asts.BinaryOp(lhs, operator, rhs) => throw AssertionError(s"unexpected $operator as binary operator")
      case Asts.Select(lhs, selected) => Select(generateSSAExpr(lhs), selected)
      case Asts.TypeTest(testedExpr, NamedTypeTree(typeName, Nil, Nil)) => HasType(generateSSAExpr(testedExpr), typeName)
      case typeTest@Asts.TypeTest(_, tpe) =>
        reportError(s"illegal type for dynamic type test: $tpe", typeTest.getPosition)
        valsCtx.valuesGen.newErrorValue()
      case expr: Asts.NonFormulaExpr => ssaInstrListOpt match {
        case None =>
          reportError("illegal expression: only formulas are allowed in this position", expr.getPosition)
          valsCtx.valuesGen.newErrorValue()
        case Some(ssaInstructionsList) =>
          generateNonFormulaExpr(expr, ssaInstructionsList, valsCtx)
      }
    }
    if (!formulaPositions.containsKey(formula)){
      expr.getPosition.foreach {
        formulaPositions.put(formula, _)
      }
    }
    formula
  }

  private def generateNonFormulaExpr(
                                      expr: Asts.NonFormulaExpr,
                                      ssaInstructionsList: mutable.ListBuffer[SSA.Instr],
                                      valsCtx: LocalValuesContext
                                    )(using util.IdentityHashMap[Formula, Position]): Formula = expr match {
    case Asts.RecordOrClassInstantiation(typeId, typeArgs, initializers) =>
      val instanceVal = valsCtx.valuesGen.newValue(typeId)
      val initializersSSAInstrList = ListBuffer.empty[Instr]
      initializers.foreach {
        case initializer@Asts.FullFieldInitializer(fieldName, rhs) =>
          initializersSSAInstrList.saveInstr(FieldWrite(instanceVal, fieldName, generateSSAExpr(rhs, Some(initializersSSAInstrList), valsCtx)), initializer)
        case initializer@Asts.ShorthandFieldInitializer(fieldName) =>
          val rhsExpr = generateSSAExpr(Asts.VariableRef(fieldName).withDesugaringSource(initializer), Some(initializersSSAInstrList), valsCtx)
          initializersSSAInstrList.saveInstr(FieldWrite(instanceVal, fieldName, rhsExpr), initializer)
      }
      ssaInstructionsList.saveInstr(
        Instantiate(instanceVal, typeId, typeArgs.map(mkType(_, valsCtx)), initializersSSAInstrList.toList), expr)
      instanceVal
    case ternary@Asts.Ternary(cond, thenBr, elseBr) =>
      val thenResVal = valsCtx.valuesGen.newValue()
      val elseResVal = valsCtx.valuesGen.newValue()
      val resultVal = valsCtx.valuesGen.newValue()
      val condFormula = generateSSAExpr(cond, Some(ssaInstructionsList), valsCtx)
      val thenFormula = generateSSAExpr(thenBr, Some(ssaInstructionsList), valsCtx)
      val elseFormula = generateSSAExpr(elseBr, Some(ssaInstructionsList), valsCtx)
      ssaInstructionsList.saveInstr(Disjunction(condFormula,
        List(Assignment(thenResVal, thenFormula)),
        List(Assignment(elseResVal, elseFormula)),
        List(Phi(resultVal, Set(thenResVal, elseResVal)))
      ), ternary)
      elseResVal
    case cast@Asts.Cast(castExpr, NamedTypeTree(typeName, Nil, Nil)) =>
      val castValue = generateSSAExprForcedAsVal(castExpr, ssaInstructionsList, valsCtx)
      val resultVal = valsCtx.valuesGen.newValue()
      ssaInstructionsList.saveInstr(Cast(resultVal, castValue, typeName), cast)
      resultVal
    case cast@Asts.Cast(castExpr, tpe) =>
      val castValue = generateSSAExprForcedAsVal(castExpr, ssaInstructionsList, valsCtx)
      reportError(s"illegal type for dynamic type test: $tpe", cast.getPosition)
      valsCtx.valuesGen.newErrorValue()
    case ascription@Asts.TypeAscription(ascribedExpr, tpe) =>
      val exprValue = generateSSAExprForcedAsVal(ascribedExpr, ssaInstructionsList, valsCtx)
      ssaInstructionsList.saveInstr(StaticTypeAssert(exprValue, mkType(tpe, valsCtx)), ascription)
      exprValue
  }

  private def mkType(typeTree: Asts.TypeTree, valsCtx: LocalValuesContext)
                    (using util.IdentityHashMap[Formula, Position]): Type = typeTree match {
    case Asts.RefinedTypeTree(baseType, predicate) =>
      val baseT = mkNominalType(baseType, valsCtx)
      val refinementCtx = valsCtx.deepCopyWithSameGlobalCtx
      val itVal = valsCtx.valuesGen.newValue(ItId)
      refinementCtx.saveOrRemap(ItId, itVal, ReassigPermission.Val, None)
      RefinedType(baseT, itVal, generateSSAExpr(predicate, None, refinementCtx))
    case basicTypeTree: Asts.BaseTypeTree =>
      mkNominalType(basicTypeTree, valsCtx)
  }

  private def mkNominalType(basicTypeTree: Asts.BaseTypeTree, valsCtx: LocalValuesContext)
                           (using util.IdentityHashMap[Formula, Position]): NominalType = basicTypeTree match {
    case Asts.PrimitiveTypeTree(primitiveType) => primitiveType
    case namedTypeTree: Asts.NamedTypeTree => mkNamedType(namedTypeTree, valsCtx)
  }

  private def mkNamedType(namedTypeTree: Asts.NamedTypeTree, valsCtx: LocalValuesContext)
                         (using util.IdentityHashMap[Formula, Position]): NamedType = {
    val Asts.NamedTypeTree(name, typeParams, params) = namedTypeTree
    NamedType(name, typeParams.map(mkType(_, valsCtx)), params.map(generateSSAExpr(_, None, valsCtx)))
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
