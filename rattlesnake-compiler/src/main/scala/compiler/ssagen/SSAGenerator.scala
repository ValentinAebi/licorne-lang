package compiler.ssagen

import compiler.analysisctx.AnalysisContext
import compiler.irs.Asts
import compiler.irs.Asts.{FormulaExpr, InterfaceDef}
import compiler.irs.SSA
import compiler.irs.SSA.{Assignment, Cast, Disjunction, Evaluate, Instantiate, Loop, Return}
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.valuesconversion.LocalValuesContext.ErrorsCallbacks
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext}
import identifiers.{ConstructorFunId, FunOrVarId, ThisId, TypeIdentifier}
import lang.*
import lang.Field.{ReassignableField, StableField}
import lang.Types.{PrimitiveTypeShape, Type}
import lang.Values.{Formula, Value}

import scala.collection.mutable

final class SSAGenerator(er: ErrorReporter) extends CompilerStep[List[Asts.Source], (Map[FunctionSignature, SSA.Function], AnalysisContext)] {

  private given ErrorsCallbacks = ErrorsCallbacks(
    unknownIdCallback = {
      case (LocalValuesContext.Unknown(id), pos) =>
        reportError(s"unknown identifier: $id", pos)
      case (LocalValuesContext.KnownButUninitialized(id, reassigStatus, typeUpperBound), pos) =>
        reportError(s"local ${reassigStatus.kw.str.toLowerCase} $id might not have been initialized at this point", pos)
    }, unexpectedStatCallback = { stat =>
      reportError("unexpected statement", stat.getPosition)
    }
  )

  override def apply(input: List[Asts.Source]): (Map[FunctionSignature, SSA.Function], AnalysisContext) = {
    val ctxBuilder = AnalysisContext.Builder(er)
    val globalValuesContext = ctxBuilder.globalValuesContext
    val valuesGen = globalValuesContext.valuesGen
    val allFunctionsCollector = mutable.Map.empty[FunctionSignature, SSA.Function]
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[Asts.DataTypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        val thisValue = valuesGen.newParam(df.id, ConstructorFunId, ThisId)
        val paramsCtx = LocalValuesContext(globalValuesContext)
        paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
        df match {
          case df@Asts.InterfaceDef(id, typeParams, functions, directSupertypes) =>
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = convertToIdToSigMapAndCheckBodyPresence(functionsMap, df.getPosition, isInterface = true)
            val sig = InterfaceSignature(id, typeParams.convert, funcs, directSupertypes.map(paramsCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ObjectDef(id, importedObjects, functions, directSupertypes) =>
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = convertToIdToSigMapAndCheckBodyPresence(functionsMap, df.getPosition, isInterface = false)
            val importedObjectsVals = mutable.LinkedHashSet.from(importedObjects.map(globalValuesContext.resolveObject))
            val sig = ObjectSignature(id, importedObjectsVals, funcs, directSupertypes.map(paramsCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ClassDef(id, typeParams, params, functions, directSupertypes) =>
            val constrParamsCtx = LocalValuesContext(globalValuesContext)
            constrParamsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            val fields = mutable.LinkedHashMap.empty[FunOrVarId, Field]
            val importedObjects = mutable.LinkedHashSet.empty[Value]
            params.foreach {
              case Asts.VarParam(paramId, paramTypeTree) =>
                fields(paramId) = ReassignableField(constrParamsCtx.mkType(paramTypeTree))
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                val paramType = constrParamsCtx.mkType(paramTypeTree)
                fields(paramId) = StableField(paramType, fieldValue)
                constrParamsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(paramType))
              case Asts.ObjectImport(objectId) =>
                importedObjects.addOne(globalValuesContext.resolveObject(objectId))
            }
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = convertToIdToSigMapAndCheckBodyPresence(functionsMap, df.getPosition, isInterface = false)
            val sig = ClassSignature(id, typeParams.convert, fields, importedObjects, funcs, directSupertypes.map(paramsCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df: Asts.DataTypeDef =>
            datatypeDefs.addOne(df)
          case Asts.StructDef(id, typeParams, fields, directSupertypes) =>
            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            val constrParamsCtx = LocalValuesContext(globalValuesContext)
            constrParamsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            fields.foreach {
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                val fieldType = constrParamsCtx.mkType(paramTypeTree)
                stableFields(paramId) = StableField(fieldType, fieldValue)
                constrParamsCtx.saveNewLocal(paramId, fieldValue, ReassigPermission.Val, Some(fieldType))
            }
            val sig = StructSignature(id, typeParams.convert, stableFields, directSupertypes)
            ctxBuilder.saveSignature(sig, df.getPosition)
            for (superT <- directSupertypes) {
              datatypeSubtypes.getOrElseUpdate(superT, mutable.LinkedHashSet.empty).addOne(id)
            }
          case df@Asts.TypeAliasDef(typeName, typeParams, params, rhs) =>
            val typeAliasParams = mutable.LinkedHashMap.empty[FunOrVarId, (Type, Value)]
            paramsCtx.saveNewLocal(ThisId, thisValue, ReassigPermission.Val, None)
            params.foreach {
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val paramValue = valuesGen.newParam(typeName, ConstructorFunId, paramId)
                val paramType = paramsCtx.mkType(paramTypeTree)
                typeAliasParams(paramId) = (paramType, paramValue)
                paramsCtx.saveNewLocal(paramId, paramValue, ReassigPermission.Val, Some(paramType))
            }
            val sig = TypeAliasSignature(typeName, typeParams.convert, thisValue, typeAliasParams)
            ctxBuilder.saveSignature(sig, df.getPosition)
        }
        for (df@Asts.DataTypeDef(id, typeParams, directSupertypes) <- datatypeDefs) {
          val sig = DatatypeSignature(id, typeParams.convert, directSupertypes, datatypeSubtypes.getOrElse(id, mutable.LinkedHashSet.empty))
          ctxBuilder.saveSignature(sig, df.getPosition)
        }
      }
    }
    (allFunctionsCollector.toMap, ctxBuilder.build())
  }

  private def collectFunctions(functionsProvider: Asts.EncapsulatedTypeDefTree, globalValsCtx: GlobalValuesContext,
                               allFunctionsCollector: mutable.Map[FunctionSignature, SSA.Function]): Map[FunOrVarId, (FunctionSignature, Option[SSA.Function])] = {
    val functions = mutable.Map.empty[FunOrVarId, (FunctionSignature, Option[SSA.Function])]
    for (func <- functionsProvider.functions) {
      if (functions.contains(func.id)) {
        reportError(s"a function named ${func.id} has already been declared in ${functionsProvider.description}", functionsProvider.getPosition)
      } else {
        val paramsInclThis = mutable.LinkedHashMap.empty[Value, Type]
        val thisVal = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, ThisId)
        val localValsCtx = LocalValuesContext(globalValsCtx)
        localValsCtx.saveNewLocal(ThisId, thisVal, ReassigPermission.Val, None)
        for (paramTree <- func.params) {
          if (localValsCtx.knows(paramTree.paramId)) {
            reportError(s"redefinition of parameter ${paramTree.paramId}", paramTree.getPosition)
          } else {
            val paramValue = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, paramTree.paramId)
            val paramType = localValsCtx.mkType(paramTree.paramTypeTree)
            paramsInclThis(paramValue) = paramType
            localValsCtx.saveNewLocal(paramTree.paramId, paramValue, ReassigPermission.Val, Some(paramType))
          }
        }
        val retType = func.optRetType match {
          case Some(retTypeTree) => localValsCtx.mkType(retTypeTree)
          case None => PrimitiveTypeShape.VoidType.toType
        }
        val sig = FunctionSignature(functionsProvider.id, func.id, func.typeParams, paramsInclThis, retType, func.visibility)
        val bodyOpt = func.bodyOpt.map(generateSSAFunc(sig, _, localValsCtx))
        functions(func.id) = (sig, bodyOpt)
        bodyOpt.foreach { body =>
          allFunctionsCollector(sig) = body
        }
      }
    }
    functions.toMap
  }

  private def convertToIdToSigMapAndCheckBodyPresence(functionsMap: Map[FunOrVarId, (FunctionSignature, Option[SSA.Function])],
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

  private def generateSSAFunc(sig: FunctionSignature, body: Asts.Block, valsCtx: LocalValuesContext): SSA.Function = {
    val ssaInstructionsList = mutable.ListBuffer.empty[SSA.Instr]
    for (stat <- body.stats) {
      generateSSA(stat, valsCtx, ssaInstructionsList)
    }
    SSA.Function(sig, ssaInstructionsList.toList)
  }

  private def generateSSA(stat: Asts.Statement, valsCtx: LocalValuesContext, ssaInstructionsList: mutable.ListBuffer[SSA.Instr]): Unit = stat match {
    case expr: Asts.Expr => ssaInstructionsList.saveInstr(Evaluate(generateSSAExpr(expr, valsCtx, ssaInstructionsList)), stat)
    case Asts.Block(stats) =>
      val blockCtx = valsCtx.withOneMoreFrame
      for (stat <- stats) {
        generateSSA(stat, blockCtx, ssaInstructionsList)
      }
    case Asts.LocalDef(localName, optTypeAnnot, rhsOpt, reassigPermission) =>
      if (valsCtx.knows(localName)) {
        reportError(s"$localName is already defined in this scope", stat.getPosition)
      } else rhsOpt match {
        case Some(rhs) =>
          val rhsFormula = generateSSAExpr(rhs, valsCtx, ssaInstructionsList)
          val localValue = forceVal(rhsFormula, valsCtx, ssaInstructionsList, rhs)
          valsCtx.saveNewLocal(localName, localValue, reassigPermission, optTypeAnnot.map(valsCtx.mkType))
          valsCtx.globalCtx.remapAsLocal(localValue, localName, stat, optTypeAnnot)
        case None =>
          valsCtx.saveNewLocal(localName, None, reassigPermission, optTypeAnnot.map(valsCtx.mkType))
      }
    case Asts.VarAssig(Asts.VariableRef(lhsLocalId), typeAnnot, rhs) =>
      if (!valsCtx.knows(lhsLocalId)) {
        reportError(s"unknown variable: $lhsLocalId", stat.getPosition)
      }
      val rhsFormula = generateSSAExpr(rhs, valsCtx, ssaInstructionsList)
      val newValue = forceVal(rhsFormula, valsCtx, ssaInstructionsList, stat)
      valsCtx.saveAssignment(lhsLocalId, newValue)
    case Asts.VarAssig(lhs, typeAnnot, rhs) => ???
    case Asts.VarModif(lhs, typeAnnot, rhs, op) => ???
    case Asts.IfThenElse(cond, thenBr, elseBrOpt) =>
      val condFormula = mkCondFormula(cond, valsCtx)
      val thenBrSSA = mutable.ListBuffer.empty[SSA.Instr]
      val thenBrCtx = valsCtx.copyWithOneMoreFrame
      generateSSA(thenBr, thenBrCtx, thenBrSSA)
      val elseBrSSA = mutable.ListBuffer.empty[SSA.Instr]
      val elseBrCtx = valsCtx.copyWithOneMoreFrame
      elseBrOpt.foreach { elseBr =>
        generateSSA(elseBr, elseBrCtx, elseBrSSA)
      }
      val phiNodes = LocalValuesContext.unificationCodeFor(valsCtx, thenBrCtx, elseBrCtx)
      ssaInstructionsList.saveInstr(Disjunction(condFormula, thenBrSSA.toList, elseBrSSA.toList, phiNodes), stat)
    case Asts.WhileLoop(cond, body) => ???
    case Asts.ForLoop(initStats, cond, stepStats, body) => ???
    case Asts.ReturnStat(optVal) =>
      val formulaOpt = optVal.map {
        generateSSAExpr(_, valsCtx, ssaInstructionsList)
      }
      ssaInstructionsList.saveInstr(Return(formulaOpt), stat)
    case Asts.PanicStat(msg) => ???
  }

  private def generateSSAExpr(expr: Asts.Expr, valsCtx: LocalValuesContext, ssaInstructionsList: mutable.ListBuffer[SSA.Instr]): Formula = expr match {
    case expr: FormulaExpr => valsCtx.mkFormula(expr)
    case Asts.FilledArrayInit(arrayElems) => ???
    case Asts.StructOrClassInstantiation(typeId, initializers) => ???
    case Asts.Ternary(cond, thenBr, elseBr) => ???
    case Asts.Cast(expr, tpe) =>
      val formulaToCast = generateSSAExpr(expr, valsCtx, ssaInstructionsList)
      val preCastVal = forceVal(formulaToCast, valsCtx, ssaInstructionsList, expr)
      val postCastVal = valsCtx.valuesGen.newIntermediate(expr)
      ssaInstructionsList.saveInstr(Cast(postCastVal, preCastVal, valsCtx.mkType(tpe)), expr)
      postCastVal
  }

  private def forceVal(formula: Formula, valsCtx: LocalValuesContext, ssaInstructionsList: mutable.ListBuffer[SSA.Instr], posNode: Asts.Ast): Value = formula match {
    case value: Value => value
    case _ =>
      val resVal = valsCtx.valuesGen.newIntermediate(posNode)
      ssaInstructionsList.saveInstr(Assignment(resVal, formula), posNode)
      resVal
  }

  extension (ssaInstructionsList: mutable.ListBuffer[SSA.Instr]) private def saveInstr(instr: SSA.Instr, node: Asts.Ast): Unit = {
    instr.setAstNode(node)
    ssaInstructionsList.addOne(instr)
  }

  private def mkCondFormula(cond: Asts.Expr, valsCtx: LocalValuesContext): Formula = {
    cond match {
      case cond: FormulaExpr => valsCtx.mkFormula(cond)
      case _ =>
        reportError("illegal expression as control-flow condition", cond.getPosition)
        valsCtx.valuesGen.newUndefined(cond)
    }
  }

  private def reportError(msg: String, posOpt: Option[Position]): Unit = {
    er.push(Err(SSAGeneration, msg, posOpt))
  }

  private def warn(msg: String, posOpt: Option[Position]): Unit = {
    er.push(Warning(SSAGeneration, msg, posOpt))
  }

}
