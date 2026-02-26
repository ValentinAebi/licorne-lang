package compiler.ssagen

import compiler.identifiers.{FunOrVarId, ItId, ThisId, TypeIdentifier}
import compiler.irs.Asts
import compiler.irs.Asts.Expr
import compiler.irs.ssa.Formulas.*
import compiler.irs.ssa.SSA
import compiler.irs.ssa.SSA.*
import compiler.lang.*
import compiler.lang.Field.{ReassignableField, StableField}
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.UnitType
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.typing.contexts.TypeVariablesContext
import compiler.util.SeqSet
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext}

import java.util
import scala.collection.mutable.ListBuffer
import scala.collection.{SeqMap, mutable}


final class SSAGenerator(er: ErrorReporter) extends CompilerStep[List[Asts.Source], (Program, TypeVariablesContext)] {

  override def apply(input: List[Asts.Source]): (Program, TypeVariablesContext) = {
    val programBuilder = Program.Builder(er)
    val globalScope = programBuilder.globalValuesContext.globalScope
    val allFunctionsCollector = mutable.SeqMap.empty[FunctionSignature, SSA.Function]
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[Asts.DataTypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        df match {
          case df@Asts.InterfaceDef(id, typeParams, functions, directSupertypes) =>
            val interfaceSigScope = Scope.nestedInside(globalScope)
            val thisValue = interfaceSigScope.newVal(ThisId)
            interfaceSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val noFunctionsSig = InterfaceSignature(id, typeParams.convert(interfaceSigScope), Map.empty, directSupertypes.map(mkNamedType(_, valsCtx)), df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = true)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ObjectDef(id, functions, directSupertypes) =>
            val objSigScope = Scope.nestedInside(globalScope)
            val thisValue = objSigScope.newVal(ThisId)
            objSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val noFunctionsSig = ObjectSignature(id, Map.empty, directSupertypes.map(mkNamedType(_, objSigScope)), df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ClassDef(id, typeParams, params, functions, directSupertypes) =>
            val classSigScope = Scope.nestedInside(globalScope)
            val thisValue = classSigScope.newVal(ThisId)
            classSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val fields = mutable.LinkedHashMap.empty[FunOrVarId, Field]
            params.foreach {
              case param@Asts.VarParam(paramId, paramTypeTree) =>
                val paramType = mkType(paramTypeTree, classSigScope)
                mustNotBeUnit(paramType, param.getPosition)
                fields(paramId) = ReassignableField(paramId, paramType)
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = classSigScope.newVal(paramId)
                val paramType = mkType(paramTypeTree, classSigScope)
                mustNotBeUnit(paramType, param.getPosition)
                fields(paramId) = StableField(paramId, paramType, fieldValue)
                classSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(paramType))
            }
            val noFunctionsSig = ClassSignature(id, typeParams.convert(classSigScope), fields, Map.empty, directSupertypes.map(mkNamedType(_, paramsCtx)), df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsCollector)
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
                                globalScope: Scope,
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

  extension (typeParams: List[Asts.TypeParamWithVariance]) private def convert(scope: Scope): List[TypeTypeParamInfo] = typeParams.map {
    case Asts.TypeParamWithVariance(id, variance, upperBounds, lowerBounds) =>
      TypeTypeParamInfo(id, variance, upperBounds.map(mkType(_, scope)), lowerBounds.map(mkType(_, scope)))
  }

  private def generateSSAFunc(
                               owner: TypeIdentifier,
                               funId: FunOrVarId,
                               bodyOpt: Option[Asts.Block],
                               funSigScope: Scope,
                               posOpt: Option[Position]
                             ): SSA.Function = bodyOpt match {
    case Some(body) =>
      val funScope = Scope.nestedInside(funSigScope)
      for (stat <- body.stats) {
        generateSSA(stat, funScope)
      }
      SSA.Function(owner, funId, Some(funScope), posOpt)
    case None =>
      SSA.Function(owner, funId, None, posOpt)
  }

  private def generateSSA(stat: Asts.Statement, currScope: Scope): Unit = {
    currScope.getLocalValuesContextUnsafe.reportHasExitedIfNeeded(er, CompilationStep.SSAGeneration, stat.getPosition)
    stat match {
      case expr: Asts.Expr =>
        val resultValue = currScope.newIntermediate("dummy")
        generateSSAExpr(resultValue, expr, currScope)

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
        ssaInstructionsList.saveInstr(AssignVal(newValue, rhsFormula), assig)
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
                               resultVal: IdValue,
                               expr: Asts.Expr,
                               currScope: Scope
                             ): Unit = {

    def recurseOnDesugared(desugaredExpr: Asts.Expr): Unit =
      generateSSAExpr(resultVal, desugaredExpr.withDesugaringSource(expr), currScope, mustBeEGraphOnly)

    def generateArgsList(argsTrees: List[Asts.Expr]): List[IdValue] = {
      val argsValsB = List.newBuilder[IdValue]
      for (argTree <- argsTrees) {
        val argVal = currScope.newIntermediate()
        argsValsB.addOne(argVal)
        generateSSAExpr(argVal, argTree, currScope)
      }
      argsValsB.result()
    }

    def generateUnary(operandTree: Asts.Expr, mkInstr: (operand: IdValue) => Instr): Unit = {
      val operandVal = currScope.newIntermediate()
      generateSSAExpr(operandVal, operandTree, currScope)
      saveInstr(mkInstr(operandVal), expr)
    }

    def generateBinary(lhs: Asts.Expr, rhs: Asts.Expr, mkInstr: (lhs: IdValue, rhs: IdValue) => Instr): Unit = {
      val lhsVal = currScope.newIntermediate()
      generateSSAExpr(lhsVal, lhs, currScope)
      val rhsVal = currScope.newIntermediate()
      generateSSAExpr(rhsVal, rhs, currScope)
      saveInstr(mkInstr(lhsVal, rhsVal), expr)
    }

    def saveInstr(instr: SSA.Instr, node: Asts.Ast): Unit = {
      instr.setAstNode(node.originalAst)
      currScope.instructions.addOne(instr)
    }

    expr match {
      case Asts.UnitLit() =>
        saveInstr(AssignVal(resultVal, currScope.valuesCtx.globalCtx.unitVal), expr)
      case Asts.IntLit(value) =>
        saveInstr(AssignIntConst(resultVal, value), expr)
      case Asts.DoubleLit(value) => ???
      case Asts.CharLit(value) => ???
      case Asts.BoolLit(value) =>
        saveInstr(AssignBoolConst(resultVal, value), expr)
      case Asts.StringLit(value) =>
        saveInstr(AssignStringConst(resultVal, value), expr)
      case varRefTree@Asts.VariableRef(name) =>
        currScope.getLocalValuesContextUnsafe.valueOf(name) match {
          case LocalValuesContext.Unknown(id) =>
            reportError(s"not found: $id", varRefTree.getPosition)
          case LocalValuesContext.KnownButUninitialized(id, reassigStatus, typeUpperBound) =>
            reportError(s"$id might not have been initialized", varRefTree.getPosition)
          case KnownAndInitialized(value, reassigStatus, typeUpperBound) =>
            saveInstr(AssignVal(resultVal, value), expr)
        }
      case Asts.ThisRef() => recurseOnDesugared(Asts.VariableRef(ThisId))
      case Asts.ItRef() => recurseOnDesugared(Asts.VariableRef(ItId))
      case Asts.ObjectRef(objectName) =>
        val objIdVal = currScope.valuesCtx.resolveObject(objectName)
        saveInstr(AssignVal(resultVal, objIdVal), expr)
      case callTree@Asts.Call(Asts.Select(receiverTree, funId), typeArgsTrees, argTrees) =>
        val receiverVal = currScope.newIntermediate()
        generateSSAExpr(receiverVal, receiverTree, currScope)
        val typeArgs = typeArgsTrees.map(mkType(_, currScope))
        val argVals = generateArgsList(argTrees)
        saveInstr(InvokeFunc(resultVal, receiverVal, InvocationTarget.Unresolved(funId), argVals), expr)
      case callTree@Asts.Call(callee@Asts.VariableRef(funId), typeArgTrees, argTrees)
        if !currScope.getLocalValuesContextUnsafe.knows(funId) =>
        val receiverVal = currScope.getLocalValuesContextUnsafe.getThisValue match {
          case Some(recv) => recv
          case None =>
            reportError(s"no receiver found for call to $funId", callTree.getPosition)
            currScope.newIntermediate()
        }
        val typeArgs = typeArgTrees.map(mkType(_, currScope))
        val argVals = generateArgsList(argTrees)
        saveInstr(InvokeFunc(resultVal, receiverVal, InvocationTarget.Unresolved(funId), argVals), expr)
      case callTree@Asts.Call(calleeTree, typeArgTrees, argTrees) =>
        if (typeArgTrees.nonEmpty) {
          reportError("type arguments on closure invocation", callTree.getPosition)
        }
        val calleeVal = currScope.newIntermediate()
        generateSSAExpr(calleeVal, calleeTree, currScope)
        val args = generateArgsList(argTrees)
        saveInstr(InvokeClosure(resultVal, calleeVal, args), expr)
      case Asts.UnaryOp(Operator.Minus, operandTree) =>
        generateUnary(operandTree, NumNeg(resultVal, _))
      case Asts.UnaryOp(Operator.ExclamationMark, operandTree) =>
        generateUnary(operandTree, LogicNeg(resultVal, _))
      case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Plus, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Add(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Minus, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Sub(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Times, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Mul(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Div, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Div(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Modulo, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Rem(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.LessThan, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Lt(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.GreaterThan, rhsTree) =>
        recurseOnDesugared(Asts.BinaryOp(rhsTree, Operator.LessThan, lhsTree).withDesugaringSource(binopTree), inScope)
      case binopTree@Asts.BinaryOp(lhsTree, Operator.LessOrEq, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Leq(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.GreaterOrEq, rhsTree) =>
        recurseOnDesugared(Asts.BinaryOp(rhsTree, Operator.LessOrEq, lhsTree).withDesugaringSource(binopTree), inScope)
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Equality, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Equal(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Inequality, rhsTree) =>
        recurseOnDesugared(Asts.UnaryOp(Operator.ExclamationMark,
          Asts.BinaryOp(lhsTree, Operator.Equality, rhsTree).withDesugaringSource(binopTree)
        ).withDesugaringSource(binopTree))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.And, rhsTree) =>
        generateBinary(lhsTree, rhsTree, And(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Or, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Or(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhs, operator, rhs) =>
        throw AssertionError(s"unexpected $operator as binary operator")
      case selectTree@Asts.Select(lhsTree, fieldId) =>
        val lhsVal = currScope.newIntermediate()
        generateSSAExpr(lhsVal, lhsTree, currScope)
        saveInstr(FieldRead(resultVal, lhsVal, FieldResolutionTarget.Unresolved(fieldId)), selectTree)
      case typeTestTree@Asts.TypeTest(testedExprTree, Asts.NamedTypeTree(typeName, Nil, Nil)) =>
        generateUnary(testedExprTree, TypeTest(resultVal, _, typeName))
      case typeTest@Asts.TypeTest(_, tpe) =>
        reportError(s"illegal type for dynamic type test: $tpe", typeTest.getPosition)
      case recordOrClassInstTree@Asts.RecordOrClassInstantiation(typeId, typeArgTrees, initializers) =>
        val instanceVal = currScope.newIntermediate()
        for (initializer <- initializers) {
          val initializerRhs = rhsOf(initializer)
          val rhsVal = currScope.newIntermediate()
          generateSSAExpr(rhsVal, initializerRhs, currScope)
        }
        val typeArgs = typeArgTrees.map(mkType(_, currScope))
        saveInstr(Instantiate(resultVal, typeId, typeArgs), recordOrClassInstTree)
      case ternaryTree@Asts.Ternary(condTree, thenTree, elseTree) =>
        val condVal = currScope.newIntermediate("cond")
        generateSSAExpr(condVal, condTree, currScope)
        val thenVal = currScope.newIntermediate("then")
        val thenScope = Scope.nestedInside(currScope)
        generateSSAExpr(thenVal, thenTree, thenScope)
        val elseVal = currScope.newIntermediate("else")
        val elseScope = Scope.nestedInside(currScope)
        generateSSAExpr(elseVal, elseTree, elseScope)
        saveInstr(Disjunction(condVal, thenScope, elseScope,
          List(DisjunctionVarData(None, thenVal, elseVal, resultVal))
        ), ternaryTree)
      case castTree@Asts.Cast(castExprTree, Asts.NamedTypeTree(typeName, Nil, Nil)) =>
        generateSSAExpr(resultVal, castExprTree, currScope)
        saveInstr(Cast(resultVal, typeName), castTree)
      case conversionTree@Asts.Cast(inExprTree, targetTypeTree: Asts.PrimitiveTypeTree) =>
        val inVal = currScope.newIntermediate()
        generateSSAExpr(inVal, inExprTree, currScope)
        saveInstr(Conversion(resultVal, inVal, targetTypeTree.primitiveType), conversionTree)
      case castTree@Asts.Cast(castExpr, tpe) =>
        reportError(s"illegal type for dynamic type test: $tpe", castTree.getPosition)
      case ascriptionTree@Asts.TypeAscription(ascribedExpr, typeTree) =>
        generateSSAExpr(resultVal, ascribedExpr, currScope)
        saveInstr(StaticTypeAssert(resultVal, mkType(typeTree, currScope)), ascriptionTree)
      case closureDefTree@Asts.ClosureDef(params, body) =>
        val bodyScope = Scope.nestedInside(currScope)
        val paramValsAndTypesB = List.newBuilder[(IdValue, Type)]
        for ((id, typeTreeOpt) <- params) {
          val paramVal = currScope.newVal(id)
          val givenTypeOpt = typeTreeOpt.map(mkType(_, bodyScope))
          val tpe = givenTypeOpt.getOrElse(TypeVariable(id.stringId, None, None) {
            bodyScope.valuesCtx.globalCtx.saveTypeVariable(_, closureDefTree.getPosition)
          })
          paramValsAndTypesB.addOne(paramVal -> tpe)
          bodyScope.getLocalValuesContextUnsafe.saveOrRemap(id, paramVal, ReassigPermission.Val, givenTypeOpt)
        }
        generateSSA(body, bodyScope)
        saveInstr(MkClosure(resultVal, paramValsAndTypesB.result(),), closureDefTree)

        val bodyCtx = valsCtx.deepCopyWithSameGlobalCtx
        val paramValsAndTypesB = List.newBuilder[(IdValue, Type)]
        for ((id, typeTreeOpt) <- params) {
          val value = valsCtx.valuesGen.newValue(id)
          val givenTypeOpt = typeTreeOpt.map(mkType(_, valsCtx))
          val tpe = givenTypeOpt.getOrElse(TypeVariable(id.stringId, None, None)(valsCtx.globalCtx.saveTypeVariable(_, closureDefTree.getPosition)))
          paramValsAndTypesB.addOne(value -> tpe)
          bodyCtx.saveOrRemap(id, value, ReassigPermission.Val, givenTypeOpt)
        }
        val closureValue = valsCtx.valuesGen.newValue()
        val bodyStats = mutable.ListBuffer.empty[Instr]
        generateSSA(body, bodyCtx, bodyStats)
        ssaInstructionsList.saveInstr(MkClosure(closureValue, paramValsAndTypesB.result(), bodyStats.toList), closureDefTree)
        closureValue
      case panicTree@Asts.PanicExpr(msg) =>
        val msgVal = generateSSAExprForcedAsVal(msg, ssaInstructionsList, valsCtx)
        ssaInstructionsList.saveInstr(Panic(msgVal), panicTree)
        valsCtx.valuesGen.newValue()
    }
  }
  
  private def generateFormula(expr: Expr, currScope: Scope): Option[Formula] = expr match {
    case Asts.IntLit(value) => Some(IntConst(value))
    case Asts.DoubleLit(value) => ???
    case Asts.UnitLit() => None
    case Asts.CharLit(value) => ???
    case Asts.BoolLit(value) => Some(BoolConst(value))
    case Asts.StringLit(value) => Some(StringConst(value))
    case Asts.VariableRef(name) => currScope.localValuesContextOpt.flatMap(_.valueOf(name).toOption)
    case Asts.ThisRef() => currScope.localValuesContextOpt.flatMap(_.getThisValue)
    case Asts.ItRef() => ???
    case Asts.ObjectRef(objectName) => currScope.valuesCtx.resolveObject(objectName)
    case Asts.TypeAscription(expr, tpe) => None
    case Asts.Call(callee, typeArgs, args) => None
    case Asts.RecordOrClassInstantiation(typeId, typeArgs, initializers) => None
    case Asts.UnaryOp(Operator.Minus, operand) =>
      for {
        opFormula <- generateFormula(operand, currScope)
      } yield Neg(opFormula)
    case _: Asts.UnaryOp => None
    case Asts.BinaryOp(lhs, Operator.Plus, rhs) =>
      for {
        lhsFormula <- generateFormula(lhs, currScope)
        rhsFormula <- generateFormula(rhs, currScope)
      } yield Sum(lhsFormula, rhsFormula)
    case Asts.BinaryOp(lhs, Operator.Minus, rhs) =>
      for {
        lhsFormula <- generateFormula(lhs, currScope)
        rhsFormula <- generateFormula(rhs, currScope)
      } yield Sum(lhsFormula, Neg(rhsFormula))
    case Asts.BinaryOp(lhs, Operator.Times, rhs) =>
      for {
        lhsFormula <- generateFormula(lhs, currScope)
        rhsFormula <- generateFormula(rhs, currScope)
      } yield Times(lhsFormula, rhsFormula)
    case Asts.BinaryOp(lhs, Operator.Div, rhs) =>
      for {
        lhsFormula <- generateFormula(lhs, currScope)
        rhsFormula <- generateFormula(rhs, currScope)
      } yield DivBy(lhsFormula, rhsFormula)
    case Asts.BinaryOp(lhs, Operator.Modulo, rhs) =>
      for {
        lhsFormula <- generateFormula(lhs, currScope)
        rhsFormula <- generateFormula(rhs, currScope)
      } yield Modulo(lhsFormula, rhsFormula)
    case _ : Asts.BinaryOp => None
    case Asts.Select(lhs, field) =>
      for {
        ownerFormula <- generateFormula(lhs, currScope)
      } yield Select(ownerFormula, field)
    case Asts.ClosureDef(params, body) => None
    case Asts.Ternary(cond, thenBr, elseBr) => None
    case Asts.Cast(expr, tpe) => None
    case Asts.TypeTest(expr, tpe) => None
    case Asts.PanicExpr(msg) => None
  }

  private def mustNotBeUnit(tpe: Type, posOpt: Option[Position]): Unit = {
    if (tpe == UnitType) {
      reportError(s"$UnitType is not allowed in this position", posOpt)
    }
  }

  private def mkType(typeTree: Asts.TypeTree, scope: Scope): Type = typeTree match {
    case typeTree: Asts.PrincipalTypeTree => mkPrincipalType(typeTree, scope)
    case typeTree: Asts.RefinedTypeTree => mkRefinedType(typeTree, scope)
  }

  private def mkPrincipalType(principalTypeTree: Asts.PrincipalTypeTree, scope: Scope): PrincipalType = principalTypeTree match {
    case Asts.PrimitiveTypeTree(primitiveType) => primitiveType
    case namedTypeTree: Asts.NamedTypeTree => mkNamedType(namedTypeTree, scope)
    case Asts.ClosureTypeTree(paramTypes, resultType) => ClosureType(paramTypes.map(mkType(_, scope)), mkType(resultType, valsCtx))
  }

  private def mkRefinedType(refinedTypeTree: Asts.RefinedTypeTree, scope: Scope): RefinedType = refinedTypeTree match {
    case Asts.IntRangeTypeTree(lowerBoundOpt, upperBoundOpt) =>
      IntRangeType(
        lowerBoundOpt.map(generateFormula(_, scope)),
        upperBoundOpt.map(generateFormula(_, scope))
      )
    case Asts.UnionTypeTree(types) =>
      UnionType(types.map(mkType(_, scope)).toSet)
    case Asts.IntersectionTypeTree(types) =>
      IntersectionType(types.map(mkType(_, scope)).toSet)
  }

  private def mkNamedType(namedTypeTree: Asts.NamedTypeTree, scope: Scope): NamedType = {
    val Asts.NamedTypeTree(name, typeParams, params) = namedTypeTree
    NamedType(name, typeParams.map(mkType(_, scope)), params.map(generateFormula(_, scope)))
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

  private def rhsOf(initializer: Asts.FieldInitializer): Asts.Expr = initializer match {
    case Asts.FullFieldInitializer(fieldName, rhs) => rhs
    case Asts.ShorthandFieldInitializer(fieldName) =>
      Asts.VariableRef(fieldName).withDesugaringSource(initializer)
  }

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Err(SSAGeneration, msg, posOpt))
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Warning(SSAGeneration, msg, posOpt))
  }

}
