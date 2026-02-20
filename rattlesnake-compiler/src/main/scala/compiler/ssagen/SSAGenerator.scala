package compiler.ssagen

import compiler.identifiers.{FunOrVarId, ItId, ThisId, TypeIdentifier}
import compiler.irs.Asts.{BinaryOp, Expr, PrincipalTypeTree, RefinedTypeTree}
import compiler.irs.ssa.SSA.*
import compiler.irs.Asts
import compiler.irs.ssa.SSA
import compiler.irs.ssa.egraphs.{EGraph, FalseNode, IdValNode, IntConstNode, NegNode, NotNode, ProductNode, SumNode, TrueNode}
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext}
import compiler.lang.Field.{ReassignableField, StableField}
import compiler.lang.Types.PrimitiveType.UnitType
import compiler.lang.*
import compiler.lang.Types.*
import compiler.typing.contexts.TypeVariablesContext
import compiler.util.SeqSet

import java.util
import scala.collection.mutable.ListBuffer
import scala.collection.{SeqMap, mutable}


final class SSAGenerator(er: ErrorReporter) extends CompilerStep[List[Asts.Source], (Program, TypeVariablesContext)] {

  override def apply(input: List[Asts.Source]): (Program, TypeVariablesContext) = {
    val programBuilder = Program.Builder(er)
    val globalValuesContext = programBuilder.globalValuesContext
    val valuesGen = globalValuesContext.valuesGen
    val allFunctionsCollector = mutable.SeqMap.empty[FunctionSignature, SSA.Function]
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[Asts.DataTypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        df match {
          case df@Asts.InterfaceDef(id, typeParams, functions, directSupertypes) =>
            val thisValue = valuesGen.newValue(ThisId)
            val valsCtx = LocalValuesContext(globalValuesContext)
            valsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val noFunctionsSig = InterfaceSignature(id, typeParams.convert(valsCtx), Map.empty, directSupertypes.map(mkNamedType(_, valsCtx)), df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = true)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ObjectDef(id, functions, directSupertypes) =>
            val thisValue = valuesGen.newValue(ThisId)
            val valsCtx = LocalValuesContext(globalValuesContext)
            valsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val noFunctionsSig = ObjectSignature(id, Map.empty, directSupertypes.map(mkNamedType(_, valsCtx)), df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ClassDef(id, typeParams, params, functions, directSupertypes) =>
            val thisValue = valuesGen.newValue(ThisId)
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val fields = mutable.LinkedHashMap.empty[FunOrVarId, Field]
            params.foreach {
              case param@Asts.VarParam(paramId, paramTypeTree) =>
                val paramType = mkType(paramTypeTree, paramsCtx)
                mustNotBeUnit(paramType, param.getPosition)
                fields(paramId) = ReassignableField(paramId, paramType)
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newValue(id)
                val paramType = mkType(paramTypeTree, paramsCtx)
                mustNotBeUnit(paramType, param.getPosition)
                fields(paramId) = StableField(paramId, paramType, fieldValue)
                paramsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(paramType))
            }
            val noFunctionsSig = ClassSignature(id, typeParams.convert(paramsCtx), fields, Map.empty, directSupertypes.map(mkNamedType(_, paramsCtx)), df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalValuesContext, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df: Asts.DataTypeDef =>
            datatypeDefs.addOne(df)
          case Asts.RecordDef(id, typeParams, fields, directSupertypes) =>
            val thisValue = valuesGen.newValue(ThisId)
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            fields.foreach {
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newValue(paramId)
                val fieldType = mkType(paramTypeTree, paramsCtx)
                mustNotBeUnit(fieldType, param.getPosition)
                stableFields(paramId) = StableField(paramId, fieldType, fieldValue)
                paramsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(fieldType))
            }
            val sig = RecordSignature(id, typeParams.convert(paramsCtx), stableFields, directSupertypes.map(mkNamedType(_, paramsCtx)), df.getPosition)
            programBuilder.saveSignature(sig, df.getPosition)
            for (superT <- directSupertypes) {
              datatypeSubtypes.getOrElseUpdate(superT.name, mutable.LinkedHashSet.empty).addOne(id)
            }
          case df@Asts.TypeAliasDef(typeName, typeParams, params, rhs) =>
            val itValue = valuesGen.newValue(ItId)
            val paramsCtx = LocalValuesContext(globalValuesContext)
            paramsCtx.saveNewLocal(ItId, itValue, ReassigPermission.Val, None)
            val typeAliasParams = mutable.LinkedHashMap.empty[FunOrVarId, (Type, IdValue)]
            params.foreach {
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val paramValue = valuesGen.newValue(paramId)
                val paramType = mkType(paramTypeTree, paramsCtx)
                typeAliasParams(paramId) = (paramType, paramValue)
                paramsCtx.saveNewLocal(paramId, paramValue, ReassigPermission.Val, Some(paramType))
            }
            val sig = TypeAliasSignature(typeName, typeParams.convert(paramsCtx), itValue, typeAliasParams, mkType(rhs, paramsCtx), df.getPosition)
            programBuilder.saveSignature(sig, df.getPosition)
        }
      }
      for (df@Asts.DataTypeDef(id, typeParams, directSupertypes) <- datatypeDefs) {
        val valsCtx = LocalValuesContext(globalValuesContext)
        val thisValue = valuesGen.newValue(ThisId)
        valsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
        val subtypes = SeqSet(datatypeSubtypes.getOrElse(id, mutable.LinkedHashSet.empty))
        val sig = DatatypeSignature(id, typeParams.convert(valsCtx), directSupertypes.map(mkNamedType(_, valsCtx)),
          subtypes, df.getPosition)
        programBuilder.saveSignature(sig, df.getPosition)
      }
    }
    val program = programBuilder.build(allFunctionsCollector)
    val typeVarsCtx = TypeVariablesContext()
    for ((tv, posOpt) <- globalValuesContext.getTypeVariables) {
      typeVarsCtx.saveTypeVariable(tv, posOpt)
    }
    er.displayAndTerminateIfErrors()
    (program, typeVarsCtx)
  }

  private def collectFunctions(
                                functionsProvider: Asts.EncapsulatedTypeDefTree,
                                functionsProviderIncompleteSig: Encapsulated,
                                globalValsCtx: GlobalValuesContext,
                                allFunctionsCollector: mutable.Map[FunctionSignature, SSA.Function]
                              ): SeqMap[FunOrVarId, (FunctionSignature, SSA.Function)] = {
    val functions = mutable.LinkedHashMap.empty[FunOrVarId, (FunctionSignature, SSA.Function)]
    for (func <- functionsProvider.functions) {
      if (functions.contains(func.id)) {
        reportError(s"a function named ${func.id} has already been declared in ${functionsProvider.description}", func.getPosition)
      } else {
        val paramsInclThis = mutable.LinkedHashMap.empty[IdValue, Type]
        val thisVal = functionsProvider match {
          case Asts.ObjectDef(id, functions, directSupertypes) => globalValsCtx.resolveObject(id)
          case _ => globalValsCtx.valuesGen.newValue(ThisId)
        }
        val funcLocalValsCtx = LocalValuesContext(globalValsCtx)
        val thisParamIsOmitted = func.params.headOption.forall(_.paramId != ThisId)
        val isObject = functionsProvider.isInstanceOf[Asts.ObjectDef]
        if (thisParamIsOmitted) {
          val thisType = NamedType(functionsProvider.id, List.empty, List.empty)
          paramsInclThis(thisVal) = thisType
          funcLocalValsCtx.saveNewLocal(ThisId, thisVal, ReassigPermission.Val, Some(thisType))
        }
        if (thisParamIsOmitted && !isObject) {
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
                  if (actualThisType.principalType != expectedThisType) {
                    reportError(s"unexpected type for receiver parameter; expected was $expectedThisType (note that it may be omitted)", func.getPosition)
                  }
                  actualThisType
                }.getOrElse(expectedThisType)
              case paramTree: Asts.NonThisFunctionParam =>
                mkType(paramTree.paramTypeTree, funcLocalValsCtx)
            }
            mustNotBeUnit(paramType, paramTree.getPosition)
            paramsInclThis(paramValue) = paramType
            val reassigPermission = if paramTree.isInstanceOf[Asts.VarParam] then ReassigPermission.Var else ReassigPermission.Val
            funcLocalValsCtx.saveNewLocal(paramTree.paramId, paramValue, reassigPermission, Some(paramType))
          }
          isFirst = false
        }
        val retType = func.optRetType match {
          case Some(retTypeTree) => mkType(retTypeTree, funcLocalValsCtx)
          case None => PrimitiveType.UnitType
        }
        val convertedTypeParams = func.typeParams.map {
          case Asts.TypeParamWithoutVariance(id, upperBoundOpt, lowerBoundOpt) =>
            FunctionTypeParamInfo(id, upperBoundOpt.map(mkType(_, funcLocalValsCtx)), lowerBoundOpt.map(mkType(_, funcLocalValsCtx)))
        }
        val ownerId = functionsProvider.id
        val funId = func.id
        val bodyOpt = generateSSAFunc(ownerId, funId, func.bodyOpt, funcLocalValsCtx, func.getPosition)
        val sig = FunctionSignature(ownerId, funId, convertedTypeParams, paramsInclThis, retType, func.visibility, func.getPosition)
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

  extension (typeParams: List[Asts.TypeParamWithVariance]) private def convert(valsCtx: LocalValuesContext): List[TypeTypeParamInfo] = typeParams.map {
    case Asts.TypeParamWithVariance(id, variance, upperBounds, lowerBounds) =>
      TypeTypeParamInfo(id, variance, upperBounds.map(mkType(_, valsCtx)), lowerBounds.map(mkType(_, valsCtx)))
  }

  private def generateSSAFunc(
                               owner: TypeIdentifier,
                               funId: FunOrVarId,
                               bodyOpt: Option[Asts.Block],
                               valsCtx: LocalValuesContext,
                               posOpt: Option[Position]
                             ): SSA.Function = bodyOpt match {
    case Some(body) =>
      val ssaInstructionsList = mutable.ListBuffer.empty[SSA.Instr]
      for (stat <- body.stats) {
        generateSSA(stat, valsCtx, ssaInstructionsList)
      }
      SSA.Function(owner, funId, Some(ssaInstructionsList.toList), posOpt)
    case None =>
      SSA.Function(owner, funId, None, posOpt)
  }

  private def generateSSA(
                           stat: Asts.Statement,
                           valsCtx: LocalValuesContext,
                           ssaInstructionsList: mutable.ListBuffer[Instr]
                         ): Unit = {

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
          generateSSAExpr(expr, ssaInstructionsList, valsCtx)
        case Asts.Block(stats) =>
          val blockCtx = valsCtx.withOneMoreFrame
          for (stat <- stats) {
            generateSSA(stat, blockCtx, ssaInstructionsList, isRepeat)
          }
        case localDef@Asts.LocalDef(localName, typeAnnotTreeOpt, rhsOpt, reassigPermission) =>
          val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, valsCtx))
          typeAnnotOpt.foreach {
            case UnitType =>
              warn(s"value of type $UnitType", localDef.getPosition)
            case _ => ()
          }
          if (valsCtx.knows(localName)) {
            reportError(s"$localName is already defined in this scope", stat.getPosition)
          } else rhsOpt match {
            case Some(rhs) =>
              generateSSA(localDef.copy(rhsOpt = None).withDesugaringSource(localDef), valsCtx, ssaInstructionsList, isRepeat)
              generateSSA(Asts.VarAssig(Asts.VariableRef(localName).withDesugaringSource(localDef), typeAnnotTreeOpt, rhs)
                .withDesugaringSource(localDef), valsCtx, ssaInstructionsList, isRepeat)
            case None =>
              typeAnnotOpt.foreach { typeAnnot =>
                ssaInstructionsList.saveInstr(LocalDecl(localName, typeAnnot), localDef)
              }
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
          val variablesB = List.newBuilder[DisjunctionVarData]
          for (varId <- externalVarsAssignedIn(ite)) {
            (thenBrCtx.valueOf(varId), elseBrCtx.valueOf(varId)) match {
              case (KnownAndInitialized(thenEndVal, _, _), KnownAndInitialized(elseEndVal, _, _)) if !thenBrCtx.hasExited && elseBrCtx.hasExited =>
                val joinVal = valsCtx.valuesGen.newValue(varId)
                variablesB.addOne(DisjunctionVarData(Some(varId), thenEndVal, elseEndVal, joinVal))
                valsCtx.remap(varId, joinVal)
              case (KnownAndInitialized(thenEndVal, _, _), _) if !thenBrCtx.hasExited =>
                valsCtx.remap(varId, thenEndVal)
              case (_, KnownAndInitialized(elseEndVal, _, _)) if !elseBrCtx.hasExited =>
                valsCtx.remap(varId, elseEndVal)
              case _ => ()
            }
          }
          ssaInstructionsList.saveInstr(Disjunction(condFormula, thenBrSSA.toList, elseBrSSA.toList, variablesB.result()), stat)
        case whileLoop@Asts.WhileLoop(cond, body) =>
          val loopUpdatedVars = externalVarsAssignedIn(whileLoop).toList.flatMap { varId =>
            valsCtx.valueOf(varId) match {
              case KnownAndInitialized(value, reassigStatus, typeUpperBound) =>
                val mkNewVal = () => valsCtx.valuesGen.newValue(varId)
                Some(LoopVarData(varId, beforeLoopVal = value, condVal = mkNewVal(), bodyLastVal = valsCtx.valuesGen.newErrorValue()))
              case _ => None
            }
          }
          val condAndBodyCtx = valsCtx.deepCopyWithSameGlobalCtx
          for (LoopVarData(id, beforeLoopVal, condVal, _) <- loopUpdatedVars) {
            condAndBodyCtx.remap(id, condVal)
          }
          val condFormula = generateSSAExpr(cond, Some(ssaInstructionsList), condAndBodyCtx)
          if (condAndBodyCtx.hasExited) {
            reportError("condition evaluation cannot terminate", cond.getPosition)
          }
          val bodySSA = mutable.ListBuffer.empty[SSA.Instr]
          generateSSA(body, condAndBodyCtx, bodySSA, isRepeat)
          if (condAndBodyCtx.exitManager.hasExited) {
            warn("loop body always exits, should be an if statement", whileLoop.getPosition)
            // give up and generate a disjunction instead
            generateSSA(
              Asts.IfThenElse(cond, body, None).withDesugaringSource(whileLoop),
              valsCtx, ssaInstructionsList, isRepeat = true
            )
          } else {
            for (loopVarData <- loopUpdatedVars) {
              loopVarData.bodyLastVal = condAndBodyCtx.valueOf(loopVarData.varId).asInstanceOf[KnownAndInitialized].value
              valsCtx.remap(loopVarData.varId, loopVarData.condVal)
            }
            ssaInstructionsList.saveInstr(Loop(condFormula, bodySSA.toList, loopUpdatedVars), whileLoop)
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
          ssaInstructionsList.saveInstr(Return(optRetVal.getOrElse(UnitVal)), stat)
          valsCtx.markHasExited()
      }
    }

    generateSSA(stat, valsCtx, ssaInstructionsList, isRepeat = false)
  }

  private def generateSSAExprForcedAsVal(
                                          expr: Asts.Expr,
                                          ssaInstructionsList: mutable.ListBuffer[Instr],
                                          valsCtx: LocalValuesContext
                                        ): IdValue =
    generateSSAExpr(expr, Some(ssaInstructionsList), valsCtx) match {
      case value: IdValue => value
      case formula =>
        val resVal = valsCtx.valuesGen.newValue()
        ssaInstructionsList.saveInstr(Assignment(resVal, formula), expr)
        resVal
    }

  private def generateTypeCheckForAnnotIfAny(
                                              rhsValue: IdValue,
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
                               ssaInstructions: mutable.ListBuffer[SSA.Instr],
                               currScope: Scope,
                               valsCtx: LocalValuesContext
                             ): IdValue = {

    def generateSSAExpr(expr: Asts.Expr): IdValue = this.generateSSAExpr(expr, ssaInstructions, currScope, valsCtx)

    def withResVal(action: IdValue => Unit): IdValue = {
      val resVal = currScope.newIntermediate()
      action(resVal)
      resVal
    }

    def binary(binop: BinaryOp)
              (action: (resVal: IdValue, lhsVal: IdValue, rhsVal: IdValue) => Unit): IdValue = withResVal { resVal =>
      action(resVal, generateSSAExpr(binop.lhs), generateSSAExpr(binop.rhs))
    }

    expr match {
      case Asts.UnitLit() =>
        valsCtx.globalCtx.unitVal
      case Asts.IntLit(value) => withResVal { resVal =>
        currScope.ctxGraph.unify(IdValNode(resVal), IntConstNode(value))
      }
      case Asts.DoubleLit(value) => ???
      case Asts.CharLit(value) => ???
      case Asts.BoolLit(true) => withResVal { resVal =>
        currScope.ctxGraph.unify(IdValNode(resVal), TrueNode)
      }
      case Asts.BoolLit(false) => withResVal { resVal =>
        currScope.ctxGraph.unify(IdValNode(resVal), FalseNode)
      }
      case Asts.StringLit(value) => withResVal { resVal =>
        // TODO interpret string literals
      }
      case varRef@Asts.VariableRef(name) =>
        valsCtx.valueOf(name) match {
          case LocalValuesContext.Unknown(id) =>
            reportError(s"not found: $id", varRef.getPosition)
            currScope.newIntermediate()
          case LocalValuesContext.KnownButUninitialized(id, reassigStatus, typeUpperBound) =>
            reportError(s"$id might not have been initialized", varRef.getPosition)
            currScope.newIntermediate()
          case KnownAndInitialized(value, reassigStatus, typeUpperBound) => value
        }
      case Asts.ThisRef() => generateSSAExpr(Asts.VariableRef(ThisId))
      case Asts.ItRef() => generateSSAExpr(Asts.VariableRef(ItId))
      case Asts.ObjectRef(objectName) => valsCtx.resolveObject(objectName)
      case call@Asts.Call(Asts.Select(receiverTree, funId), typeArgsTrees, argsTrees) =>
        val receiverVal = generateSSAExpr(receiverTree)
        val typeArgs = typeArgsTrees.map(mkType(_, valsCtx))
        val args = argsTrees.map(generateSSAExpr)
        withResVal { resVal =>
          InvokeFunc(resVal, receiverVal, InvocationTarget.Unresolved(funId), args)
        }
      case call@Asts.Call(callee@Asts.VariableRef(funId), typeArgTrees, argTrees) if !valsCtx.knows(funId) =>
        val receiverVal = valsCtx.getThisValue match {
          case Some(recv) => recv
          case None =>
            reportError(s"no receiver found for call to $funId", call.getPosition)
            currScope.newIntermediate()
        }
        val typeArgs = typeArgTrees.map(mkType(_, valsCtx))
        val args = argTrees.map(generateSSAExpr)
        withResVal { resVal =>
          InvokeFunc(resVal, receiverVal, InvocationTarget.Unresolved(funId), args)
        }
      case call@Asts.Call(calleeTree, typeArgTrees, argTrees) =>
        if (typeArgTrees.nonEmpty) {
          reportError("type arguments on closure invocation", call.getPosition)
        }
        val callee = generateSSAExpr(calleeTree)
        val args = argTrees.map(generateSSAExpr)
        withResVal { resVal =>
          InvokeClosure(resVal, callee, args)
        }
      case Asts.UnaryOp(Operator.Minus, operandTree) => withResVal { resVal =>
        val operand = generateSSAExpr(operandTree)
        val operandId = currScope.ctxGraph.classOf(IdValNode(operand))
        currScope.ctxGraph.unify(IdValNode(resVal), NegNode(operandId))
      }
      case Asts.UnaryOp(Operator.ExclamationMark, operandTree) => withResVal { resVal =>
        val operand = generateSSAExpr(operandTree)
        val operandId = currScope.ctxGraph.classOf(IdValNode(operand))
        currScope.ctxGraph.unify(IdValNode(resVal), NotNode(operandId))
      }
      case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
      case binop@Asts.BinaryOp(lhsTree, Operator.Plus, rhsTree) => binary(binop) { (resVal, lhsVal, rhsVal) =>
        val lhsId = currScope.ctxGraph.classOf(IdValNode(lhsVal))
        val rhsId = currScope.ctxGraph.classOf(IdValNode(rhsVal))
        currScope.ctxGraph.unify(IdValNode(resVal), SumNode(SeqSet(lhsId, rhsId)))
      }
      case binop@Asts.BinaryOp(lhs, Operator.Minus, rhs) => binary(binop) { (resVal, lhsVal, rhsVal) =>
        val lhsId = currScope.ctxGraph.classOf(IdValNode(lhsVal))
        val rhsId = currScope.ctxGraph.classOf(IdValNode(rhsVal))
        val negRhsId = currScope.ctxGraph.classOf(NegNode(rhsId))
        currScope.ctxGraph.unify(IdValNode(resVal), SumNode(SeqSet(lhsId, negRhsId)))
      }
      case binop@Asts.BinaryOp(lhs, Operator.Times, rhs) => binary(binop){ (resVal, lhsVal, rhsVal) =>
        val lhsId = currScope.ctxGraph.classOf(IdValNode(lhsVal))
        val rhsId = currScope.ctxGraph.classOf(IdValNode(rhsVal))
        currScope.ctxGraph.unify(IdValNode(resVal), ProductNode(SeqSet(lhsId, rhsId)))
      }
      case binop@Asts.BinaryOp(lhs, Operator.Div, rhs) => binary(binop) { (resVal, lhsVal, rhsVal) =>
        // TODO check rhsVal != 0: StaticAssert? More specialized node?
        ssaInstructions.saveInstr(StaticAssert())
        val lhsId = currScope.ctxGraph.classOf(IdValNode(lhsVal))
        val rhsId = currScope.ctxGraph.classOf(IdValNode(rhsVal))
        
      }
      case binop@Asts.BinaryOp(lhs, Operator.Modulo, rhs) => Rem(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case binop@Asts.BinaryOp(lhs, Operator.GreaterThan, rhs) => LessThan(generateSSAExpr(rhs), generateSSAExpr(lhs))
      case binop@Asts.BinaryOp(lhs, Operator.LessThan, rhs) => LessThan(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case binop@Asts.BinaryOp(lhs, Operator.GreaterOrEq, rhs) => LessOrEq(generateSSAExpr(rhs), generateSSAExpr(lhs))
      case binop@Asts.BinaryOp(lhs, Operator.LessOrEq, rhs) => LessOrEq(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case binop@Asts.BinaryOp(lhs, Operator.Equality, rhs) => Equal(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case binop@Asts.BinaryOp(lhs, Operator.Inequality, rhs) => Not(Equal(generateSSAExpr(lhs), generateSSAExpr(rhs)))
      case binop@Asts.BinaryOp(lhs, Operator.And, rhs) => And(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case binop@Asts.BinaryOp(lhs, Operator.Or, rhs) => Or(generateSSAExpr(lhs), generateSSAExpr(rhs))
      case binop@Asts.BinaryOp(lhs, operator, rhs) => throw AssertionError(s"unexpected $operator as binary operator")
      case binop@Asts.Select(lhs, selected) => Select(generateSSAExpr(lhs), UnresolvedField(selected))
      case binop@Asts.TypeTest(testedExpr, Asts.NamedTypeTree(typeName, Nil, Nil)) => HasType(generateSSAExpr(testedExpr), typeName)
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
  }

  private def generateNonFormulaExpr(
                                      expr: Asts.NonFormulaExpr,
                                      ssaInstructionsList: mutable.ListBuffer[SSA.Instr],
                                      valsCtx: LocalValuesContext
                                    ): Formula = expr match {
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
      val condFormula = generateSSAExpr(cond, Some(ssaInstructionsList), valsCtx)
      val thenInstrList = mutable.ListBuffer.empty[Instr]
      val elseInstrList = mutable.ListBuffer.empty[Instr]
      val thenResVal = generateSSAExprForcedAsVal(thenBr, thenInstrList, valsCtx)
      val elseResVal = generateSSAExprForcedAsVal(elseBr, elseInstrList, valsCtx)
      val resultVal = valsCtx.valuesGen.newValue()
      ssaInstructionsList.saveInstr(Disjunction(condFormula,
        thenInstrList.toList,
        elseInstrList.toList,
        List(DisjunctionVarData(None, thenResVal, elseResVal, resultVal))
      ), ternary)
      resultVal
    case cast@Asts.Cast(castExpr, Asts.NamedTypeTree(typeName, Nil, Nil)) =>
      val castValue = generateSSAExprForcedAsVal(castExpr, ssaInstructionsList, valsCtx)
      ssaInstructionsList.saveInstr(Cast(castValue, typeName), cast)
      castValue
    case conversion@Asts.Cast(castExpr, targetTypeTree: Asts.PrimitiveTypeTree) =>
      val castValue = generateSSAExprForcedAsVal(castExpr, ssaInstructionsList, valsCtx)
      val resultVal = valsCtx.valuesGen.newValue()
      ssaInstructionsList.saveInstr(Conversion(resultVal, castValue, targetTypeTree.primitiveType), conversion)
      resultVal
    case cast@Asts.Cast(castExpr, tpe) =>
      val castValue = generateSSAExprForcedAsVal(castExpr, ssaInstructionsList, valsCtx)
      reportError(s"illegal type for dynamic type test: $tpe", cast.getPosition)
      valsCtx.valuesGen.newErrorValue()
    case ascription@Asts.TypeAscription(ascribedExpr, tpe) =>
      val exprValue = generateSSAExprForcedAsVal(ascribedExpr, ssaInstructionsList, valsCtx)
      ssaInstructionsList.saveInstr(StaticTypeAssert(exprValue, mkType(tpe, valsCtx)), ascription)
      exprValue
    case closureDef@Asts.ClosureDef(params, body) =>
      val bodyCtx = valsCtx.deepCopyWithSameGlobalCtx
      val paramValsAndTypesB = List.newBuilder[(IdValue, Type)]
      for ((id, typeTreeOpt) <- params) {
        val value = valsCtx.valuesGen.newValue(id)
        val givenTypeOpt = typeTreeOpt.map(mkType(_, valsCtx))
        val tpe = givenTypeOpt.getOrElse(TypeVariable(id.stringId, None, None)(valsCtx.globalCtx.saveTypeVariable(_, closureDef.getPosition)))
        paramValsAndTypesB.addOne(value -> tpe)
        bodyCtx.saveOrRemap(id, value, ReassigPermission.Val, givenTypeOpt)
      }
      val closureValue = valsCtx.valuesGen.newValue()
      val bodyStats = mutable.ListBuffer.empty[Instr]
      generateSSA(body, bodyCtx, bodyStats)
      ssaInstructionsList.saveInstr(MkClosure(closureValue, paramValsAndTypesB.result(), bodyStats.toList), closureDef)
      closureValue
    case panic@Asts.PanicExpr(msg) =>
      val msgVal = generateSSAExprForcedAsVal(msg, ssaInstructionsList, valsCtx)
      ssaInstructionsList.saveInstr(Panic(msgVal), panic)
      valsCtx.valuesGen.newValue()
  }

  private def mustNotBeUnit(tpe: Type, posOpt: Option[Position]): Unit = {
    if (tpe == UnitType) {
      reportError(s"$UnitType is not allowed in this position", posOpt)
    }
  }

  private def mkType(typeTree: Asts.TypeTree, valsCtx: LocalValuesContext): Type = typeTree match {
    case typeTree: Asts.PrincipalTypeTree => mkPrincipalType(typeTree, valsCtx)
    case typeTree: Asts.RefinedTypeTree => mkRefinedType(typeTree, valsCtx)
  }

  private def mkPrincipalType(principalTypeTree: PrincipalTypeTree, valsCtx: LocalValuesContext): PrincipalType = principalTypeTree match {
    case Asts.PrimitiveTypeTree(primitiveType) => primitiveType
    case namedTypeTree: Asts.NamedTypeTree => mkNamedType(namedTypeTree, valsCtx)
    case Asts.ClosureTypeTree(paramTypes, resultType) => ClosureType(paramTypes.map(mkType(_, valsCtx)), mkType(resultType, valsCtx))
  }

  private def mkRefinedType(refinedTypeTree: RefinedTypeTree, valsCtx: LocalValuesContext): RefinedType = refinedTypeTree match {
    case Asts.IntRangeTypeTree(lowerBoundOpt, upperBoundOpt) =>
      IntRangeType(lowerBoundOpt.map(generateSSAExpr(_, None, valsCtx)), upperBoundOpt.map(generateSSAExpr(_, None, valsCtx)))
    case Asts.UnionTypeTree(types) =>
      UnionType(types.map(mkType(_, valsCtx)).toSet)
    case Asts.IntersectionTypeTree(types) =>
      IntersectionType(types.map(mkType(_, valsCtx)).toSet)
  }

  private def mkNamedType(namedTypeTree: Asts.NamedTypeTree, valsCtx: LocalValuesContext): NamedType = {
    val Asts.NamedTypeTree(name, typeParams, params) = namedTypeTree
    NamedType(name, typeParams.map(mkType(_, valsCtx)), params.map(generateSSAExpr(_, None, valsCtx)))
  }

  private def externalVarsAssignedIn(ast: Asts.Ast): Set[FunOrVarId] = {
    val assigned = mutable.Set.empty[FunOrVarId]
    val defined = mutable.Set.empty[FunOrVarId]
    ast.preorderWalk {
      case localDef: Asts.LocalDef =>
        defined.addOne(localDef.localName)
      case assignment: Asts.Assignment => assignment.lhs match {
        case Asts.VariableRef(varId) =>
          assigned.addOne(varId)
        case _ => ()
      }
      case _ => ()
    }
    val assignedVars = assigned.toSet -- defined
    assignedVars
  }

  extension (ssaInstructionsList: mutable.ListBuffer[SSA.Instr]) private def saveInstr(instr: SSA.Instr, node: Asts.Ast): Unit = {
    instr.setAstNode(node.originalAst)
    ssaInstructionsList.addOne(instr)
  }

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Err(SSAGeneration, msg, posOpt))
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Warning(SSAGeneration, msg, posOpt))
  }

}
