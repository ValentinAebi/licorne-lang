package compiler.ssagen

import compiler.analysisctx.AnalysisContext
import compiler.irs.Asts
import compiler.irs.Asts.{FormulaExpr, InterfaceDef}
import compiler.irs.SSA
import compiler.irs.SSA.{Assignment, Cast, Disjunction, Evaluate, Instantiate}
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.valuesconversion.LocalValuesContext.UnknownIdCallback
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext}
import identifiers.{ConstructorFunId, FunOrVarId, ThisId, TypeIdentifier}
import lang.*
import lang.Field.{ReassignableField, StableField}
import lang.Types.{PrimitiveTypeShape, Type}
import lang.Values.{Formula, Value}

import scala.collection.mutable

final class SSAGenerator(er: ErrorReporter) extends CompilerStep[List[Asts.Source], (Map[FunctionSignature, SSA.Function], AnalysisContext)] {

  private given UnknownIdCallback = UnknownIdCallback {
    case (LocalValuesContext.Unknown(id), pos) =>
      reportError(s"unknown identifier: $id", pos)
    case (LocalValuesContext.KnownButUninitialized(id, reassigStatus), pos) =>
      reportError(s"local ${reassigStatus.kw.str.toLowerCase} $id might not have been initialized at this point", pos)
  }

  override def apply(input: List[Asts.Source]): (Map[FunctionSignature, SSA.Function], AnalysisContext) = {
    val ctxBuilder = AnalysisContext.Builder(er)
    val globalValuesContext = ctxBuilder.globalValuesContext
    val valuesGen = globalValuesContext.valuesGen
    val allFunctionsCollector = mutable.Map.empty[FunctionSignature, SSA.Function]
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[Asts.DataTypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        // Fake this. The typechecker should ensure later that no element in the signature refers to this.
        val fakeThis = valuesGen.newUndefined(df)
        // Fake context for conversion of supertypes. The typechecker should ensure later that the supertypes are actually not dependent.
        val fakeCtx = LocalValuesContext(fakeThis, globalValuesContext)
        df match {
          case df@Asts.InterfaceDef(id, typeParams, functions, directSupertypes) =>
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = convertToIdToSigMapAndCheckBodyPresence(functionsMap, df.getPosition, isInterface = true)
            val sig = InterfaceSignature(id, typeParams.convert, funcs, directSupertypes.map(fakeCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ObjectDef(id, importedObjects, functions, directSupertypes) =>
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = convertToIdToSigMapAndCheckBodyPresence(functionsMap, df.getPosition, isInterface = false)
            val importedObjectsVals = mutable.LinkedHashSet.from(importedObjects.map(globalValuesContext.resolveObject))
            val sig = ObjectSignature(id, importedObjectsVals, funcs, directSupertypes.map(fakeCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@Asts.ClassDef(id, typeParams, params, functions, directSupertypes) =>
            val constrParamsCtx = LocalValuesContext(fakeThis, globalValuesContext)
            val fields = mutable.LinkedHashMap.empty[FunOrVarId, Field]
            val importedObjects = mutable.LinkedHashSet.empty[Value]
            params.foreach {
              case Asts.VarParam(paramId, paramTypeTree) =>
                fields(paramId) = ReassignableField(constrParamsCtx.mkType(paramTypeTree))
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                fields(paramId) = StableField(constrParamsCtx.mkType(paramTypeTree), fieldValue)
                constrParamsCtx(paramId) = (fieldValue, ReassigStatus.Val)
              case Asts.ObjectImport(objectId) =>
                importedObjects.addOne(globalValuesContext.resolveObject(objectId))
            }
            val functionsMap = collectFunctions(df, globalValuesContext, allFunctionsCollector)
            val funcs = convertToIdToSigMapAndCheckBodyPresence(functionsMap, df.getPosition, isInterface = false)
            val sig = ClassSignature(id, typeParams.convert, fields, importedObjects, funcs, directSupertypes.map(fakeCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df: Asts.DataTypeDef =>
            datatypeDefs.addOne(df)
          case Asts.StructDef(id, typeParams, fields, directSupertypes) =>
            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            val constrParamsCtx = LocalValuesContext(fakeThis, globalValuesContext)
            fields.foreach {
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                stableFields(paramId) = StableField(constrParamsCtx.mkType(paramTypeTree), fieldValue)
                constrParamsCtx(paramId) = (fieldValue, ReassigStatus.Val)
            }
            val sig = StructSignature(id, typeParams.convert, stableFields, directSupertypes)
            ctxBuilder.saveSignature(sig, df.getPosition)
            for (superT <- directSupertypes) {
              datatypeSubtypes.getOrElseUpdate(superT, mutable.LinkedHashSet.empty).addOne(id)
            }
          case df@Asts.TypeAliasDef(typeName, typeParams, params, rhs) =>
            val thisValue = valuesGen.newTypeAliasParam(typeName, ThisId)
            val typeAliasParams = mutable.LinkedHashMap.empty[FunOrVarId, (Type, Value)]
            val paramsCtx = LocalValuesContext(thisValue, globalValuesContext)
            params.foreach {
              case Asts.SimpleParam(paramId, paramTypeTree) =>
                val paramValue = valuesGen.newTypeAliasParam(typeName, paramId)
                typeAliasParams(paramId) = (paramsCtx.mkType(paramTypeTree), paramValue)
                paramsCtx(paramId) = (paramValue, ReassigStatus.Val)
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
                               allFunctions: mutable.Map[FunctionSignature, SSA.Function]): Map[FunOrVarId, (FunctionSignature, Option[SSA.Function])] = {
    val functions = mutable.Map.empty[FunOrVarId, (FunctionSignature, Option[SSA.Function])]
    for (func <- functionsProvider.functions) {
      if (functions.contains(func.id)) {
        reportError(s"a function named ${func.id} has already been declared in ${functionsProvider.description}", functionsProvider.getPosition)
      } else {
        val paramsInclThis = mutable.LinkedHashMap.empty[Value, Type]
        val thisVal = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, ThisId)
        val localValsCtx = LocalValuesContext(thisVal, globalValsCtx)
        for (paramTree <- func.params) {
          if (localValsCtx.knows(paramTree.paramId)) {
            reportError(s"redefinition of parameter ${paramTree.paramId}", paramTree.getPosition)
          } else {
            val paramValue = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, paramTree.paramId)
            paramsInclThis(paramValue) = localValsCtx.mkType(paramTree.paramTypeTree)
            localValsCtx(paramTree.paramId) = (paramValue, ReassigStatus.Val)
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
          allFunctions(sig) = body
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
      generateSSA(stat, valsCtx, None, ssaInstructionsList)
    }
    SSA.Function(sig, ssaInstructionsList.toList)
  }

  private def generateSSA(stat: Asts.Statement, valsCtx: LocalValuesContext, pendingValue: Option[Value], ssaInstructionsList: mutable.ListBuffer[SSA.Instr]): Unit = {

    def saveInstr(instr: SSA.Instr): Unit = {
      instr.setAstNode(stat)
      ssaInstructionsList.addOne(instr)
    }

    def consumeExpr(formula: Formula): Unit = saveInstr(pendingValue match {
      case Some(value) => Assignment(value, formula)
      case None => Evaluate(formula)
    })

    stat match {
      case expr: Asts.FormulaExpr => consumeExpr(valsCtx.mkFormula(expr))
      case Asts.FilledArrayInit(arrayElems) => ???
      case Asts.StructOrClassInstantiation(typeId, initializers) =>
        val newObjValue = valsCtx.valuesGen.newIntermediate(stat)
        saveInstr(Instantiate(newObjValue, typeId))
      case Asts.Ternary(cond, thenBr, elseBr) =>
        val condFormula = mkCondFormula(cond, valsCtx)
        val thenBrSSA = mutable.ListBuffer.empty[SSA.Instr]
        generateSSA(thenBr, valsCtx.withOneMoreLayer, pendingValue, thenBrSSA)
        val elseBrSSA = mutable.ListBuffer.empty[SSA.Instr]
        generateSSA(elseBr, valsCtx.withOneMoreLayer, pendingValue, elseBrSSA)
        saveInstr(Disjunction(condFormula, thenBrSSA.toList, elseBrSSA.toList, List.empty))
      case Asts.Cast(expr, tpe) =>
        val inVal = valsCtx.valuesGen.newIntermediate(expr)
        generateSSA(expr, valsCtx, Some(inVal), ssaInstructionsList)
        val castVal = pendingValue.getOrElse(valsCtx.valuesGen.newIntermediate(stat))
        saveInstr(Cast(castVal, inVal, valsCtx.mkType(tpe)))
      case Asts.TypeTest(expr, tpe) => ???
      case Asts.Block(stats) =>
        if (pendingValue.isDefined) {
          reportError("expected an expression, found a block", stat.getPosition)
        }
        val blockCtx = valsCtx.withOneMoreLayer
        for (stat <- stats) {
          generateSSA(stat, blockCtx, None, ssaInstructionsList)
        }
      case Asts.LocalDef(localName, optTypeAnnot, rhsOpt, reassigStatus) =>
        if (valsCtx.knows(localName)){
          reportError(s"$localName is already defined in this scope", stat.getPosition)
        } else {
          val value = valsCtx.valuesGen.newLocal(localName, stat, optTypeAnnot)
          rhsOpt.foreach { rhs =>
            generateSSA(rhs, valsCtx, Some(value), ssaInstructionsList)
          }
          valsCtx(localName) = (value, reassigStatus, optTypeAnnot.map(valsCtx.mkType))
        }
      case Asts.VarAssig(Asts.VariableRef(lhsLocalId), typeAnnot, rhs) =>
        if (!valsCtx.knows(lhsLocalId)){
          reportError(s"unknown variable: $lhsLocalId", stat.getPosition)
        }
        val assignedValue = valsCtx.valuesGen.newLocal(lhsLocalId, stat, typeAnnot)
        generateSSA(rhs, valsCtx, Some(assignedValue), ssaInstructionsList)
        val rs = if valsCtx.isReassignable(lhsLocalId).getOrElse(true) then ReassigStatus.Var else ReassigStatus.Val
        valsCtx(lhsLocalId) = (assignedValue, rs, typeAnnot.map(valsCtx.mkType))
      case Asts.VarAssig(lhs, typeAnnot, rhs) => ???
      case Asts.VarModif(lhs, typeAnnot, rhs, op) => ???
      case Asts.IfThenElse(cond, thenBr, elseBrOpt) =>
        val condFormula = mkCondFormula(cond, valsCtx)
        // contexts do not need to be copied since if branches can only be blocks
        val thenBrSSA = mutable.ListBuffer.empty[SSA.Instr]
        generateSSA(thenBr, valsCtx, pendingValue, thenBrSSA)
        val elseBrSSA = mutable.ListBuffer.empty[SSA.Instr]
        elseBrOpt.foreach { elseBr =>
          generateSSA(elseBr, valsCtx, pendingValue, elseBrSSA)
        }
        
        saveInstr(Disjunction(condFormula, thenBrSSA.toList, elseBrSSA.toList, ))
      case Asts.WhileLoop(cond, body) => ???
      case Asts.ForLoop(initStats, cond, stepStats, body) => ???
      case Asts.ReturnStat(optVal) => ???
      case Asts.PanicStat(msg) => ???
    }
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
