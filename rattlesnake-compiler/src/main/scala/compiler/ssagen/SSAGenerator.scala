package compiler.ssagen

import compiler.identifiers.{FunOrVarId, ItId, ThisId, TypeIdentifier}
import compiler.irs.Asts.Expr
import compiler.irs.SSA.*
import compiler.irs.{Asts, SSA}
import compiler.lang.*
import compiler.lang.Field.{ReassignableField, StableField}
import compiler.lang.Formulas.*
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{BoolType, UnitType}
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.recurrences.Recurrence
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.typing.contexts.TypeVariablesContext
import compiler.util.SeqSet
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.LocalValuesContext
import compiler.valuesconversion.LocalValuesContext.KnownAndInitialized

import scala.collection.{SeqMap, mutable}
import scala.util.boundary


final class SSAGenerator(typeVarsCtx: TypeVariablesContext, proxyStore: ProxyStore, er: ErrorReporter) extends CompilerStep[List[Asts.Source], Program] {

  private type SeqMapBuilder[A, B] = mutable.Builder[(A, B), SeqMap[A, B]]

  private given CompilationStep = CompilationStep.SSAGeneration

  override def apply(input: List[Asts.Source]): Program = {
    val programBuilder = Program.Builder(er)
    val globalScope = programBuilder.globalValuesContext.globalScope
    val allFunctionsB = SeqMap.newBuilder[FunctionSignature, SSA.Function]
    val loopsCollector = mutable.ListBuffer.empty[SSA.Loop]
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[Asts.DataTypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        df match {
          case df@Asts.InterfaceDef(id, typeParamTrees, functions, directSupertypes) =>
            val interfaceSigScope = Scope.nestedInside(globalScope)
            val thisValue = interfaceSigScope.newVal(ThisId)
            interfaceSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val noFunctionsSig = InterfaceSignature(id, typeParamTrees.convert(interfaceSigScope), Map.empty, directSupertypes.map(mkNamedType(_, interfaceSigScope)), interfaceSigScope, df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsB)(using loopsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = true)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ObjectDef(id, functions, directSupertypes) =>
            val objSigScope = Scope.nestedInside(globalScope)
            val thisValue = objSigScope.newVal(ThisId)
            objSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val noFunctionsSig = ObjectSignature(id, Map.empty, directSupertypes.map(mkNamedType(_, objSigScope)), objSigScope, df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsB)(using loopsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ClassDef(id, typeParamTrees, params, functions, directSupertypes) =>
            val classSigScope = Scope.nestedInside(globalScope)
            val thisValue = classSigScope.newVal(ThisId)
            classSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val typeParams = typeParamTrees.convert(classSigScope)
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
            val noFunctionsSig = ClassSignature(id, typeParams, fields, Map.empty, directSupertypes.map(mkNamedType(_, classSigScope)), classSigScope, df.getPosition)
            val functionsMap = collectFunctions(df, noFunctionsSig, globalScope, allFunctionsB)(using loopsCollector)
            val funcs = createIdToSigMapAndCheckBodyExists(functionsMap, df.getPosition, isInterface = false)
            val sig = noFunctionsSig.copy(functions = funcs)
            programBuilder.saveSignature(sig, df.getPosition)
          case df: Asts.DataTypeDef =>
            datatypeDefs.addOne(df)
          case Asts.RecordDef(id, typeParamTrees, fields, directSupertypes) =>
            val recordSigScope = Scope.nestedInside(globalScope)
            val thisValue = recordSigScope.newVal(ThisId)
            recordSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val typeParams = typeParamTrees.convert(recordSigScope)
            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            fields.foreach {
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = recordSigScope.newVal(paramId)
                val fieldType = mkType(paramTypeTree, recordSigScope)
                mustNotBeUnit(fieldType, param.getPosition)
                stableFields(paramId) = StableField(paramId, fieldType, fieldValue)
                recordSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(fieldType))
            }
            val sig = RecordSignature(id, typeParams, stableFields, directSupertypes.map(mkNamedType(_, recordSigScope)), recordSigScope, df.getPosition)
            programBuilder.saveSignature(sig, df.getPosition)
            for (superT <- directSupertypes) {
              datatypeSubtypes.getOrElseUpdate(superT.name, mutable.LinkedHashSet.empty).addOne(id)
            }
          case df@Asts.TypeAliasDef(typeName, typeParamTrees, params, rhs) =>
            val typeAliasSigScope = Scope.nestedInside(globalScope)
            val itValue = typeAliasSigScope.newVal(ItId)
            typeAliasSigScope.getLocalValuesContextUnsafe.saveNewLocal(ItId, itValue, ReassigPermission.Val, None)
            val typeParams = typeParamTrees.convert(typeAliasSigScope)
            val typeAliasParams = mutable.LinkedHashMap.empty[FunOrVarId, (Type, IdValue)]
            params.foreach {
              case param@Asts.SimpleParam(paramId, paramTypeTree) =>
                val paramValue = typeAliasSigScope.newVal(paramId)
                val paramType = mkType(paramTypeTree, typeAliasSigScope)
                typeAliasParams(paramId) = (paramType, paramValue)
                typeAliasSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramId, paramValue, ReassigPermission.Val, Some(paramType))
            }
            val sig = TypeAliasSignature(typeName, typeParams, itValue, typeAliasParams, mkType(rhs, typeAliasSigScope), typeAliasSigScope, df.getPosition)
            programBuilder.saveSignature(sig, df.getPosition)
        }
      }
      for (df@Asts.DataTypeDef(id, typeParamTrees, directSupertypes) <- datatypeDefs) {
        val datatypeSigScope = Scope.nestedInside(globalScope)
        val thisValue = datatypeSigScope.newVal(ThisId)
        datatypeSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
        val typeParams = typeParamTrees.convert(datatypeSigScope)
        val subtypes = SeqSet(datatypeSubtypes.getOrElse(id, mutable.LinkedHashSet.empty))
        val sig = DatatypeSignature(id, typeParams, directSupertypes.map(mkNamedType(_, datatypeSigScope)),
          subtypes, datatypeSigScope, df.getPosition)
        programBuilder.saveSignature(sig, df.getPosition)
      }
    }
    val program = programBuilder.build(allFunctionsB.result(), loopsCollector.toSeq)
    for ((tv, posOpt) <- globalScope.globalValuesCtx.getTypeVariables) {
      typeVarsCtx.saveTypeVariable(tv, posOpt)
    }
    println(proxyStore) // TODO remove (debug)
    er.displayAndTerminateIfErrors()
    program
  }

  private def collectFunctions(
                                functionsProvider: Asts.EncapsulatedTypeDefTree,
                                functionsProviderIncompleteSig: EncapsulatedTypeSig,
                                globalScope: Scope,
                                allFunctionsB: SeqMapBuilder[FunctionSignature, SSA.Function]
                              )(using loopsCollector: mutable.ListBuffer[SSA.Loop]): SeqMap[FunOrVarId, (FunctionSignature, SSA.Function)] = {
    val functions = mutable.LinkedHashMap.empty[FunOrVarId, (FunctionSignature, SSA.Function)]
    for (funDef <- functionsProvider.functions) {
      if (functions.contains(funDef.id)) {
        reportError(s"a function named ${funDef.id} has already been declared in ${functionsProvider.description}", funDef.getPosition)
      } else {
        val funSigScope = Scope.nestedInside(globalScope)
        val paramsInclThis = mutable.LinkedHashMap.empty[NamedIdValue, Type]
        val thisVal = functionsProvider match {
          case Asts.ObjectDef(id, functions, directSupertypes) => funSigScope.valuesCtx.resolveObject(id)
          case _ => funSigScope.newVal(ThisId)
        }
        val thisParamIsOmitted = funDef.params.headOption.forall(_.paramId != ThisId)
        val isObject = functionsProvider.isInstanceOf[Asts.ObjectDef]
        if (thisParamIsOmitted) {
          val thisType = NamedType(functionsProvider.id, List.empty, List.empty)
          paramsInclThis(thisVal) = thisType
          funSigScope.getLocalValuesContextUnsafe.saveNewLocal(ThisId, thisVal, ReassigPermission.Val, Some(thisType))
        }
        if (thisParamIsOmitted && !isObject) {
          reportError(s"parameters list of ${funDef.id} should start with the receiver parameter (syntax: 'this : Type')", funDef.getPosition)
        } else if (!thisParamIsOmitted && isObject) {
          warn("receiver parameter can be omitted inside objects", funDef.getPosition)
        }
        var isFirst = true
        for (paramTree <- funDef.params) {
          if (funSigScope.getLocalValuesContextUnsafe.knows(paramTree.paramId)) {
            reportError(s"redefinition of parameter ${paramTree.paramId}", paramTree.getPosition)
          } else {
            val paramValue = funSigScope.newParam(paramTree.paramId)
            val paramType = paramTree match {
              case Asts.ThisParam(paramTypeTreeOpt) =>
                if (!isFirst) {
                  reportError("receiver parameter should always be at the beginning of the parameters list", funDef.getPosition)
                }
                val expectedThisType = functionsProviderIncompleteSig.toType(Map.empty)
                paramTypeTreeOpt.map { paramTypeTree =>
                  val actualThisType = mkType(paramTypeTree, funSigScope)
                  // TODO see if we allow refined types on receiver
                  if (actualThisType != expectedThisType) {
                    reportError(s"unexpected type for receiver parameter; expected was $expectedThisType (note that it may be omitted)", funDef.getPosition)
                  }
                  actualThisType
                }.getOrElse(expectedThisType)
              case paramTree: Asts.NonThisFunctionParam =>
                mkType(paramTree.paramTypeTree, funSigScope)
            }
            mustNotBeUnit(paramType, paramTree.getPosition)
            paramsInclThis(paramValue) = paramType
            val reassigPermission = if paramTree.isInstanceOf[Asts.VarParam] then ReassigPermission.Var else ReassigPermission.Val
            funSigScope.getLocalValuesContextUnsafe.saveNewLocal(paramTree.paramId, paramValue, reassigPermission, Some(paramType))
            proxyStore.saveProxy(paramValue, paramValue)
          }
          isFirst = false
        }
        val retType = funDef.optRetType match {
          case Some(retTypeTree) => mkType(retTypeTree, funSigScope)
          case None => PrimitiveType.UnitType
        }
        val convertedTypeParams = funDef.typeParams.map {
          case Asts.TypeParamWithoutVariance(id, upperBoundOpt, lowerBoundOpt) =>
            FunctionTypeParamInfo(id, upperBoundOpt.map(mkType(_, funSigScope)), lowerBoundOpt.map(mkType(_, funSigScope)))
        }
        val ownerId = functionsProvider.id
        val funId = funDef.id
        val function = generateSSAFunc(ownerId, funId, funDef.bodyOpt, funSigScope, funDef.getPosition)
        val sig = FunctionSignature(ownerId, funId, convertedTypeParams, paramsInclThis, retType, funSigScope, funDef.visibility, funDef.getPosition)
        functions(funDef.id) = (sig, function)
        allFunctionsB.addOne(sig -> function)
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
                             )(using loopsCollector: mutable.ListBuffer[SSA.Loop]): SSA.Function = bodyOpt match {
    case Some(body) =>
      val funScope = Scope.nestedInside(funSigScope)
      for (stat <- body.stats) {
        generateSSA(stat, funScope)
      }
      SSA.Function(owner, funId, Some(funScope))
    case None =>
      SSA.Function(owner, funId, None)
  }

  private def generateSSA(stat: Asts.Statement, currScope: Scope, newScopeIfBlock: Boolean = true)(using loopsCollector: mutable.ListBuffer[SSA.Loop]): Unit = {
    currScope.getLocalValuesContextUnsafe.reportHasExitedIfNeeded(er, CompilationStep.SSAGeneration, stat.getPosition)
    stat match {
      case expr: Asts.Expr =>
        val resultValue = currScope.newIntermediate("dummy")
        generateSSAExpr(resultValue, expr, currScope)
        currScope.saveInstr(Drop(resultValue), expr)
      case block@Asts.Block(stats) =>
        val blockScope = if (newScopeIfBlock) {
          val sc = Scope.nestedInside(currScope)
          currScope.saveInstr(sc, block)
          sc
        } else currScope
        for (stat <- stats) {
          generateSSA(stat, blockScope)
        }
      case localDef@Asts.LocalDef(localName, typeAnnotTreeOpt, rhsOpt, reassigPermission) =>
        val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, currScope))
        typeAnnotOpt.foreach {
          case UnitType =>
            warn(s"value of type $UnitType", localDef.getPosition)
          case _ => ()
        }
        if (currScope.getLocalValuesContextUnsafe.knows(localName)) {
          reportError(s"$localName is already defined in this scope", stat.getPosition)
        } else rhsOpt match {
          case Some(rhs) =>
            generateSSA(localDef.copy(rhsOpt = None).withDesugaringSource(localDef), currScope)
            generateSSA(Asts.VarAssig(Asts.VariableRef(localName).withDesugaringSource(localDef), typeAnnotTreeOpt, rhs)
              .withDesugaringSource(localDef), currScope)
          case None =>
            typeAnnotOpt.foreach { typeAnnot =>
              currScope.saveInstr(LocalDecl(localName, typeAnnot), localDef)
            }
            currScope.getLocalValuesContextUnsafe.saveNewLocal(localName, None, reassigPermission, typeAnnotOpt)
        }
      case assig@Asts.VarAssig(Asts.VariableRef(lhsLocalId), typeAnnotTreeOpt, rhsTree) =>
        if (!currScope.getLocalValuesContextUnsafe.knows(lhsLocalId)) {
          reportError(s"unknown variable: $lhsLocalId", stat.getPosition)
        }
        if (!currScope.getLocalValuesContextUnsafe.isReassignableOrUnknown(lhsLocalId)
          && currScope.getLocalValuesContextUnsafe.valueOf(lhsLocalId).isInstanceOf[KnownAndInitialized]) {
          reportError(s"illegal reassignment of value $lhsLocalId", assig.getPosition)
        }
        val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, currScope))
        val newValue = currScope.newIntermediate()
        generateSSAExpr(newValue, rhsTree, currScope)
        currScope.getLocalValuesContextUnsafe.remap(lhsLocalId, newValue)
        generateTypeCheckForAnnotIfAny(newValue, typeAnnotOpt, currScope, assig)
      case assig@Asts.VarAssig(Asts.Select(ownerTree, fieldId), typeAnnotTreeOpt, rhsTree) =>
        val ownerVal = currScope.newIntermediate()
        generateSSAExpr(ownerVal, ownerTree, currScope)
        val typeAnnotOpt = typeAnnotTreeOpt.map(mkType(_, currScope))
        val rhsVal = currScope.newIntermediate()
        generateSSAExpr(rhsVal, rhsTree, currScope)
        generateTypeCheckForAnnotIfAny(rhsVal, typeAnnotOpt, currScope, assig)
        currScope.saveInstr(FieldWrite(ownerVal, FieldResolutionTarget.Unresolved(fieldId), rhsVal), assig)
      case assig@Asts.VarAssig(lhs, typeAnnotOpt, rhs) =>
        reportError("assignment target is not valid", assig.getPosition)
      case Asts.VarModif(lhs@Asts.VariableRef(lhsLocalId), typeAnnot, rhs, op) =>
        generateSSA(Asts.VarAssig(lhs, typeAnnot,
          Asts.BinaryOp(lhs, op, rhs).withDesugaringSource(stat)
        ).withDesugaringSource(stat), currScope)
      case Asts.VarModif(lhs, typeAnnot, rhs, op) =>
        reportError("in-place mutation is only allowed on local variables", stat.getPosition)
      case ite@Asts.IfThenElse(condTree, thenTree, elseTreeOpt) =>
        val condVal = currScope.newIntermediate("cond")
        generateSSAExpr(condVal, condTree, currScope)
        val thenScope = Scope.nestedInside(currScope)
        generateSSA(thenTree, thenScope, newScopeIfBlock = false)
        val elseScope = Scope.nestedInside(currScope)
        elseTreeOpt.foreach { elseTree =>
          generateSSA(elseTree, elseScope, newScopeIfBlock = false)
        }
        val variablesB = List.newBuilder[DisjunctionVarData]
        for (varId <- externalVarsAssignedIn(ite)) {
          (thenScope.getLocalValuesContextUnsafe.valueOf(varId), elseScope.getLocalValuesContextUnsafe.valueOf(varId)) match {
            case (KnownAndInitialized(thenEndVal, _, _), KnownAndInitialized(elseEndVal, _, _)) if !thenScope.hasExited && !elseScope.hasExited =>
              val joinVal = currScope.newVar(varId)
              variablesB.addOne(DisjunctionVarData(Some(varId), thenEndVal, elseEndVal, joinVal))
              currScope.getLocalValuesContextUnsafe.remap(varId, joinVal)
            case (KnownAndInitialized(thenEndVal, _, _), _) if !thenScope.hasExited =>
              currScope.getLocalValuesContextUnsafe.remap(varId, thenEndVal)
            case (_, KnownAndInitialized(elseEndVal, _, _)) if !elseScope.hasExited =>
              currScope.getLocalValuesContextUnsafe.remap(varId, elseEndVal)
            case _ => ()
          }
        }
        currScope.saveInstr(Disjunction(condVal, thenScope, elseScope, variablesB.result()), stat)
      case whileLoop@Asts.WhileLoop(condTree, bodyTree) =>
        val condScope = Scope.nestedInside(currScope)
        val bodyScope = Scope.nestedInside(condScope)
        val loopUpdatedVars = externalVarsAssignedIn(whileLoop).toList.flatMap { varId =>
          currScope.getLocalValuesContextUnsafe.valueOf(varId) match {
            case KnownAndInitialized(value, _, _) =>
              Some(LoopVarData(varId, beforeLoopVal = value, condVal = condScope.newVar(varId),
                bodyLastVal = bodyScope.newVar(varId)))
            case _ => None
          }
        }
        for (LoopVarData(id, beforeLoopVal, condVal, _) <- loopUpdatedVars) {
          condScope.getLocalValuesContextUnsafe.remap(id, condVal)
        }
        val condVal = currScope.newIntermediate("cond")
        generateSSAExpr(condVal, condTree, condScope)
        if (condScope.hasExited) {
          reportError("condition evaluation cannot terminate", condTree.getPosition)
        }
        generateSSA(bodyTree, bodyScope, newScopeIfBlock = false)
        if (bodyScope.hasExited) {
          warn("loop body always exits, should be an if statement", whileLoop.getPosition)
          // give up and generate a disjunction instead
          generateSSA(
            Asts.IfThenElse(condTree, bodyTree, None).withDesugaringSource(whileLoop),
            currScope
          )
        } else {
          for (varData@LoopVarData(varId, beforeLoopVal, condVal, bodyLastVal) <- loopUpdatedVars) {
            val bodyLastLocalVal = bodyScope.getLocalValuesContextUnsafe.valueOf(varId).asInstanceOf[KnownAndInitialized].value
            varData.recurrenceOpt = for {
              init <- proxyStore.getProxy(beforeLoopVal)
              induct <- proxyStore.getProxy(bodyLastLocalVal)
            } yield Recurrence(init, induct, condVal)
            bodyScope.instructions.addOne(AssignVal(bodyLastVal, bodyLastLocalVal))
            currScope.getLocalValuesContextUnsafe.remap(varId, condVal)
          }
          val loop = Loop(condScope, condVal, bodyScope, loopUpdatedVars)
          currScope.saveInstr(loop, whileLoop)
          loopsCollector.addOne(loop)
        }
      case forLoop@Asts.ForLoop(initStats, cond, stepStats, body) =>
        generateSSA(Asts.Block(
          initStats :+ Asts.WhileLoop(cond, Asts.Block(
            body +: stepStats
          ).withDesugaringSource(forLoop)).withDesugaringSource(forLoop)
        ).withDesugaringSource(forLoop), currScope)
      case returnStat@Asts.ReturnStat(returnedTreeOpt) =>
        val retVal = currScope.newIntermediate("ret")
        returnedTreeOpt match {
          case Some(returnedTree) =>
            generateSSAExpr(retVal, returnedTree, currScope)
          case None =>
            currScope.saveInstr(AssignVal(retVal, currScope.valuesCtx.globalCtx.unitVal), returnStat)
        }
        currScope.saveInstr(Return(retVal), stat)
        currScope.getLocalValuesContextUnsafe.markHasExited()
    }
  }

  private def generateTypeCheckForAnnotIfAny(
                                              rhsValue: IdValue,
                                              typeAnnotOpt: Option[Type],
                                              scope: Scope,
                                              astNode: Asts.Ast
                                            ): Unit = {
    typeAnnotOpt.foreach { typeAnnot =>
      scope.saveInstr(StaticTypeAssert(rhsValue, typeAnnot), astNode)
    }
  }

  private def generateSSAExpr(
                               resultVal: IdValue,
                               expr: Asts.Expr,
                               currScope: Scope
                             )(using loopsCollector: mutable.ListBuffer[SSA.Loop]): Option[Formula] = {

    def recurseOnDesugared(desugaredExpr: Asts.Expr): Option[Formula] =
      generateSSAExpr(resultVal, desugaredExpr.withDesugaringSource(expr), currScope)

    def generateArgsList(argsTrees: List[Asts.Expr]): List[IdValue] = {
      val argsValsB = List.newBuilder[IdValue]
      for (argTree <- argsTrees) {
        val argVal = currScope.newIntermediate()
        argsValsB.addOne(argVal)
        generateSSAExpr(argVal, argTree, currScope)
      }
      argsValsB.result()
    }

    def generateUnary(operandTree: Asts.Expr, mkInstr: (operand: IdValue) => Instr, mkFormulaOpt: Option[Formula => Formula] = None): Option[Formula] = {
      val operandVal = currScope.newIntermediate()
      val proxyOfOperandOpt = generateSSAExpr(operandVal, operandTree, currScope)
      currScope.saveInstr(mkInstr(operandVal), expr)
      for {
        mkFormula <- mkFormulaOpt
        proyOfOperand <- proxyOfOperandOpt
      } yield mkFormula(proyOfOperand)
    }

    def generateUnaryWithProxy(operandTree: Asts.Expr, mkInstr: (operand: IdValue) => Instr, mkFormula: Formula => Formula): Option[Formula] =
      generateUnary(operandTree, mkInstr, Some(mkFormula))

    def generateBinary(lhs: Asts.Expr, rhs: Asts.Expr, mkInstr: (lhs: IdValue, rhs: IdValue) => Instr, mkFormulaOpt: Option[(Formula, Formula) => Formula] = None): Option[Formula] = {
      val lhsVal = currScope.newIntermediate()
      val lhsProxyOpt = generateSSAExpr(lhsVal, lhs, currScope)
      val rhsVal = currScope.newIntermediate()
      val rhsProxyOpt = generateSSAExpr(rhsVal, rhs, currScope)
      currScope.saveInstr(mkInstr(lhsVal, rhsVal), expr)
      for {
        mkFormula <- mkFormulaOpt
        lhsProxy <- lhsProxyOpt
        rhsProxy <- rhsProxyOpt
      } yield mkFormula(lhsProxy, rhsProxy)
    }

    def generateBinaryWithProxy(lhs: Asts.Expr, rhs: Asts.Expr, mkInstr: (lhs: IdValue, rhs: IdValue) => Instr, mkFormula: (Formula, Formula) => Formula): Option[Formula] =
      generateBinary(lhs, rhs, mkInstr, Some(mkFormula))

    val proxyOpt = expr match {
      case Asts.UnitLit() =>
        currScope.saveInstr(AssignVal(resultVal, currScope.valuesCtx.globalCtx.unitVal), expr)
        None
      case Asts.IntLit(value) =>
        currScope.saveInstr(AssignIntConst(resultVal, value), expr)
        Some(IntConst(value))
      case Asts.DoubleLit(value) => ???
      case Asts.CharLit(value) => ???
      case Asts.BoolLit(value) =>
        currScope.saveInstr(AssignBoolConst(resultVal, value), expr)
        None
      case Asts.StringLit(value) =>
        currScope.saveInstr(AssignStringConst(resultVal, value), expr)
        None
      case varRefTree@Asts.VariableRef(name) =>
        currScope.getLocalValuesContextUnsafe.valueOf(name) match {
          case LocalValuesContext.Unknown(id) =>
            reportError(s"not found: $id", varRefTree.getPosition)
            None
          case LocalValuesContext.KnownButUninitialized(id, _, _) =>
            reportError(s"$id might not have been initialized", varRefTree.getPosition)
            None
          case KnownAndInitialized(value, _, _) =>
            currScope.saveInstr(AssignVal(resultVal, value), expr)
            Some(value)
        }
      case Asts.ThisRef() =>
        recurseOnDesugared(Asts.VariableRef(ThisId))
        None
      case Asts.ItRef() =>
        recurseOnDesugared(Asts.VariableRef(ItId))
        None // TODO update if it gets reintroduced
      case Asts.ObjectRef(objectName) =>
        val objIdVal = currScope.valuesCtx.resolveObject(objectName)
        currScope.saveInstr(AssignVal(resultVal, objIdVal), expr)
        None
      case callTree@Asts.Call(Asts.Select(receiverTree, funId), typeArgsTrees, argTrees) =>
        val receiverVal = currScope.newIntermediate()
        generateSSAExpr(receiverVal, receiverTree, currScope)
        val typeArgs = typeArgsTrees.map(mkType(_, currScope))
        val argVals = generateArgsList(argTrees)
        currScope.saveInstr(InvokeFunc(resultVal, receiverVal, InvocationTarget.Unresolved(funId), typeArgs, argVals), expr)
        None
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
        currScope.saveInstr(InvokeFunc(resultVal, receiverVal, InvocationTarget.Unresolved(funId), typeArgs, argVals), expr)
        None
      case callTree@Asts.Call(calleeTree, typeArgTrees, argTrees) =>
        if (typeArgTrees.nonEmpty) {
          reportError("type arguments on closure invocation", callTree.getPosition)
        }
        val calleeVal = currScope.newIntermediate()
        generateSSAExpr(calleeVal, calleeTree, currScope)
        val args = generateArgsList(argTrees)
        currScope.saveInstr(InvokeClosure(resultVal, calleeVal, args), expr)
        None
      case Asts.UnaryOp(Operator.Minus, operandTree) =>
        generateUnaryWithProxy(operandTree, NumNeg(resultVal, _), Neg(_))
      case Asts.UnaryOp(Operator.ExclamationMark, operandTree) =>
        generateUnary(operandTree, LogicNeg(resultVal, _))
      case Asts.UnaryOp(operator, operand) => throw AssertionError(s"unexpected $operator as unary operator")
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Plus, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Add(resultVal, _, _), Plus(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Minus, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Sub(resultVal, _, _), (a, b) => Plus(a, Neg(b)))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Times, rhsTree) =>
        // TODO see if we keep the proxy or not: non-determinism?
        generateBinaryWithProxy(lhsTree, rhsTree, Mul(resultVal, _, _), Times(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Div, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Div(resultVal, _, _)) // TODO proxy?
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Modulo, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Rem(resultVal, _, _)) // TODO proxy?
      case binopTree@Asts.BinaryOp(lhsTree, Operator.LessThan, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Lt(resultVal, _, _), LessOrEq(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.GreaterThan, rhsTree) =>
        recurseOnDesugared(Asts.BinaryOp(rhsTree, Operator.LessThan, lhsTree).withDesugaringSource(binopTree))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.LessOrEq, rhsTree) =>
        generateBinaryWithProxy(lhsTree, rhsTree, Leq(resultVal, _, _), LessOrEq(_, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.GreaterOrEq, rhsTree) =>
        recurseOnDesugared(Asts.BinaryOp(rhsTree, Operator.LessOrEq, lhsTree).withDesugaringSource(binopTree))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Equality, rhsTree) =>
        generateBinary(lhsTree, rhsTree, Equal(resultVal, _, _))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Inequality, rhsTree) =>
        recurseOnDesugared(Asts.UnaryOp(Operator.ExclamationMark,
          Asts.BinaryOp(lhsTree, Operator.Equality, rhsTree).withDesugaringSource(binopTree)
        ).withDesugaringSource(binopTree))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.And, rhsTree) =>
        recurseOnDesugared(Asts.Ternary(lhsTree,
          Asts.TypeAscription(rhsTree, Asts.PrimitiveTypeTree(BoolType).withDesugaringSource(binopTree)).withDesugaringSource(binopTree),
          Asts.BoolLit(false).withDesugaringSource(binopTree)
        ).withDesugaringSource(binopTree))
      case binopTree@Asts.BinaryOp(lhsTree, Operator.Or, rhsTree) =>
        recurseOnDesugared(Asts.Ternary(lhsTree,
          Asts.BoolLit(true).withDesugaringSource(binopTree),
          Asts.TypeAscription(rhsTree, Asts.PrimitiveTypeTree(BoolType).withDesugaringSource(binopTree)).withDesugaringSource(binopTree)
        ))
      case binopTree@Asts.BinaryOp(lhs, operator, rhs) =>
        throw AssertionError(s"unexpected $operator as binary operator")
      case selectTree@Asts.Select(lhsTree, fieldId) =>
        val lhsVal = currScope.newIntermediate()
        generateSSAExpr(lhsVal, lhsTree, currScope)
        currScope.saveInstr(FieldRead(resultVal, lhsVal, FieldResolutionTarget.Unresolved(fieldId)), selectTree)
        None
      case typeTestTree@Asts.TypeTest(testedExprTree, Asts.NamedTypeTree(typeName, Nil, Nil)) =>
        generateUnaryWithProxy(testedExprTree, TypeTest(resultVal, _, typeName), TypePredicate(_, typeName))
      case typeTest@Asts.TypeTest(_, tpe) =>
        reportError(s"illegal type for dynamic type test: $tpe", typeTest.getPosition)
        None
      case recordOrClassInstTree@Asts.RecordOrClassInstantiation(typeId, typeArgTrees, initializers) =>
        val initializationScope = Scope.nestedInside(currScope)
        for (initializer <- initializers) {
          val initializerRhs = rhsOf(initializer)
          val rhsVal = currScope.newIntermediate()
          generateSSAExpr(rhsVal, initializerRhs, currScope)
          initializationScope.saveInstr(FieldWrite(resultVal, FieldResolutionTarget.Unresolved(initializer.fieldName), rhsVal), initializer)
        }
        val typeArgs = typeArgTrees.map(mkType(_, currScope))
        currScope.saveInstr(Instantiate(resultVal, typeId, typeArgs), recordOrClassInstTree)
        currScope.saveInstr(initializationScope, recordOrClassInstTree)
        None
      case ternaryTree@Asts.Ternary(condTree, thenTree, elseTree) =>
        val condVal = currScope.newIntermediate("cond")
        generateSSAExpr(condVal, condTree, currScope)
        val thenVal = currScope.newIntermediate("then")
        val thenScope = Scope.nestedInside(currScope)
        generateSSAExpr(thenVal, thenTree, thenScope)
        val elseVal = currScope.newIntermediate("else")
        val elseScope = Scope.nestedInside(currScope)
        generateSSAExpr(elseVal, elseTree, elseScope)
        currScope.saveInstr(Disjunction(condVal, thenScope, elseScope,
          List(DisjunctionVarData(None, thenVal, elseVal, resultVal))
        ), ternaryTree)
        // retrieve info from lowering
        proxyStore.getProxy(thenVal) match {
          case Some(BoolConst(true)) => Some(LogicalOr(condVal, elseVal))
          case _ => proxyStore.getProxy(elseVal) match {
            case Some(BoolConst(false)) => Some(LogicalAnd(condVal, thenVal))
            case _ => None
          }
        }
      case castTree@Asts.Cast(castExprTree, Asts.NamedTypeTree(typeName, Nil, Nil)) =>
        generateSSAExpr(resultVal, castExprTree, currScope)
        currScope.saveInstr(Cast(resultVal, typeName), castTree)
        None
      case conversionTree@Asts.Cast(inExprTree, targetTypeTree: Asts.PrimitiveTypeTree) =>
        val inVal = currScope.newIntermediate()
        generateSSAExpr(inVal, inExprTree, currScope)
        currScope.saveInstr(Conversion(resultVal, inVal, targetTypeTree.primitiveType), conversionTree)
        None
      case castTree@Asts.Cast(castExpr, tpe) =>
        reportError(s"illegal type for dynamic type test: $tpe", castTree.getPosition)
        None
      case ascriptionTree@Asts.TypeAscription(ascribedExpr, typeTree) =>
        generateSSAExpr(resultVal, ascribedExpr, currScope)
        currScope.saveInstr(StaticTypeAssert(resultVal, mkType(typeTree, currScope)), ascriptionTree)
        None
      case closureDefTree@Asts.ClosureDef(params, body) =>
        val bodyScope = Scope.nestedInside(currScope)
        val paramValsAndTypesB = List.newBuilder[(ValIdValue, Type)]
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
        currScope.saveInstr(MkClosure(resultVal, paramValsAndTypesB.result(), bodyScope), closureDefTree)
        None
      case panicTree@Asts.PanicExpr(msgTree) =>
        val msgVal = currScope.newIntermediate("msg")
        generateSSAExpr(msgVal, msgTree, currScope)
        currScope.saveInstr(Panic(msgVal), panicTree)
        currScope.getLocalValuesContextUnsafe.markHasExited()
        None
    }
    if (!proxyStore.hasProxyFor(resultVal)) {
      // avoid resetting proxy when generateSSAExpr is called recursively
      proxyStore.saveProxy(resultVal, proxyOpt)
    }
    proxyOpt
  }

  private def generateFormula(expr: Expr, currScope: Scope): Option[Formula] = boundary {

    def generateFormula(expr: Expr, currScope: Scope): Option[Formula] = {

      def failIllegalConstruct(constructKindDescr: String): Option[Formula] = {
        er.reportError(s"illegal construct in formula: $constructKindDescr", expr.getPosition)
        None
      }

      expr match {
        case Asts.IntLit(value) => Some(IntConst(value))
        case Asts.DoubleLit(value) => ???
        case Asts.UnitLit() => failIllegalConstruct("unit literal")
        case Asts.CharLit(value) => ???
        case Asts.BoolLit(value) => Some(BoolConst(value))
        case Asts.StringLit(value) => Some(StringConst(value))
        case Asts.VariableRef(name) => currScope.getLocalValuesContextOpt.flatMap(_.valueOf(name).toOption)
        case Asts.ThisRef() => currScope.getLocalValuesContextOpt.flatMap(_.getThisValue)
        case Asts.ItRef() => ???
        case Asts.ObjectRef(objectName) => Some(currScope.valuesCtx.resolveObject(objectName))
        case Asts.TypeAscription(expr, tpe) => failIllegalConstruct("type ascription")
        // TODO check that there are no side-effects (later)
        // TODO non-prefixed calls (implicit this)?
        case Asts.Call(callee, typeArgs, args) =>
          val receiverAndFunIdOpt = callee match {
            case Asts.VariableRef(funId) =>
              currScope.getLocalValuesContextOpt.flatMap(_.getThisValue).map(_ -> funId)
            case Asts.Select(lhs, funId) =>
              generateFormula(lhs, currScope).map(_ -> funId)
            case _ => failIllegalConstruct("closure invocation")
          }
          receiverAndFunIdOpt match {
            case Some((receiverFormula, funId)) =>
              val argFormulas = args.flatMap(generateFormula(_, currScope))
              if argFormulas.size == args.size then Some(Call(receiverFormula, InvocationTarget.Unresolved(funId), argFormulas))
              else None
            case _ => None
          }
        case Asts.RecordOrClassInstantiation(typeId, typeArgs, initializers) => failIllegalConstruct("instantiation")
        case Asts.UnaryOp(Operator.Minus, operand) =>
          for {
            opFormula <- generateFormula(operand, currScope)
          } yield Neg(opFormula)
        case expr: Asts.UnaryOp => failIllegalConstruct(s"\"${expr.operator}\" operator")
        case Asts.BinaryOp(lhs, Operator.Plus, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield Plus(lhsFormula, rhsFormula)
        case Asts.BinaryOp(lhs, Operator.Minus, rhs) =>
          for {
            lhsFormula <- generateFormula(lhs, currScope)
            rhsFormula <- generateFormula(rhs, currScope)
          } yield Plus(lhsFormula, Neg(rhsFormula))
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
        case expr: Asts.BinaryOp => failIllegalConstruct(s"\"${expr.operator}\" operator")
        case Asts.Select(lhs, field) =>
          for {
            ownerFormula <- generateFormula(lhs, currScope)
          } yield Select(ownerFormula, FieldResolutionTarget.Unresolved(field))
        case Asts.ClosureDef(params, body) => failIllegalConstruct("closure definition")
        case Asts.Ternary(cond, thenBr, elseBr) => failIllegalConstruct("ternary operator")
        case Asts.Cast(expr, tpe) => failIllegalConstruct("dynamic cast or conversion")
        // TODO ideally should be allowed
        case Asts.TypeTest(expr, tpe) => failIllegalConstruct("type test")
        case Asts.PanicExpr(msg) => failIllegalConstruct("panic expression")
      }
    }

    generateFormula(expr, currScope)
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
    case Asts.ClosureTypeTree(paramTypes, resultType) => ClosureType(paramTypes.map(mkType(_, scope)), mkType(resultType, scope))
  }

  private def mkRefinedType(refinedTypeTree: Asts.RefinedTypeTree, scope: Scope): RefinedType = refinedTypeTree match {
    case Asts.IntRangeTypeTree(lowerBoundOpt, upperBoundOpt) =>
      IntRangeType(
        lowerBoundOpt.flatMap(generateFormula(_, scope)),
        upperBoundOpt.flatMap(generateFormula(_, scope))
      )
    case Asts.UnionTypeTree(types) =>
      UnionType(SeqSet(types.map(mkType(_, scope))))
    case Asts.IntersectionTypeTree(types) =>
      IntersectionType(SeqSet(types.map(mkType(_, scope))))
  }

  private def mkNamedType(namedTypeTree: Asts.NamedTypeTree, scope: Scope): NamedType = {
    val Asts.NamedTypeTree(name, typeParams, params) = namedTypeTree
    NamedType(name, typeParams.map(mkType(_, scope)), params.flatMap(generateFormula(_, scope)))
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

  extension (scope: Scope) private def saveInstr(instr: SSA.Instr, node: Asts.Ast): Unit = {
    instr.setAstNode(node.originalAst)
    scope.instructions.addOne(instr)
  }

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Err(SSAGeneration, msg, posOpt))
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.report(Warning(SSAGeneration, msg, posOpt))
  }

}
