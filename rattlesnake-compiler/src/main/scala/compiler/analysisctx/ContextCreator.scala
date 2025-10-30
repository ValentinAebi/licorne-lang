package compiler.analysisctx

import compiler.irs.Asts.*
import compiler.pipeline.CompilationStep.ContextCreation
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.valuesconversion.{GlobalValuesContext, LocalValuesContext, ValuesGenerator}
import identifiers.{ConstructorFunId, FunOrVarId, ThisId, TypeIdentifier}
import lang.Field.{ReassignableField, StableField}
import lang.{ClassSignature, DatatypeSignature, Field, FunctionSignature, InterfaceSignature, ObjectSignature, StructSignature, TypeAliasSignature, Variance}
import lang.Types.{PrimitiveTypeShape, Type}
import lang.Values.Value

import scala.collection.mutable

final class ContextCreator(er: ErrorReporter) extends CompilerStep[List[Source], (List[Source], AnalysisContext)] {

  override def apply(input: List[Source]): (List[Source], AnalysisContext) = {
    val ctxBuilder = AnalysisContext.Builder(er)
    val globalValuesContext = ctxBuilder.globalValuesContext
    val valuesGen = globalValuesContext.valuesGen
    for (src <- input) {
      val datatypeDefs = mutable.ListBuffer.empty[DatatypeDef]
      val datatypeSubtypes = mutable.Map.empty[TypeIdentifier, mutable.LinkedHashSet[TypeIdentifier]]
      for (df <- src.defs) {
        // Fake this. The typechecker should ensure later that no element in the signature refers to this.
        val fakeThis = valuesGen.newUndefined(df)
        // Fake context for conversion of supertypes. The typechecker should ensure later that the supertypes are actually not dependent.
        val fakeCtx = LocalValuesContext(fakeThis, globalValuesContext)
        df match {
          case df@InterfaceDef(id, typeParams, functions, directSupertypes) =>
            val functionSigs = collectFunctions(df, globalValuesContext)
            val sig = InterfaceSignature(id, typeParams.convert, functionSigs, directSupertypes.map(fakeCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@ObjectDef(id, importedObjects, functions, directSupertypes) =>
            val functionSigs = collectFunctions(df, globalValuesContext)
            val importedObjectsVals = mutable.LinkedHashSet.from(importedObjects.map(globalValuesContext.resolveObject))
            val sig = ObjectSignature(id, importedObjectsVals, functionSigs, directSupertypes.map(fakeCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df@ClassDef(id, typeParams, params, functions, directSupertypes) =>
            val constrParamsCtx = LocalValuesContext(fakeThis, globalValuesContext)
            val fields = mutable.LinkedHashMap.empty[FunOrVarId, Field]
            val importedObjects = mutable.LinkedHashSet.empty[Value]
            params.foreach {
              case VarParam(paramId, paramTypeTree) =>
                fields(paramId) = ReassignableField(constrParamsCtx.mkType(paramTypeTree))
              case SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                fields(paramId) = StableField(constrParamsCtx.mkType(paramTypeTree), fieldValue)
                constrParamsCtx(paramId) = fieldValue
              case ObjectImport(objectId) =>
                importedObjects.addOne(globalValuesContext.resolveObject(objectId))
            }
            val funSigs = collectFunctions(df, globalValuesContext)
            val sig = ClassSignature(id, typeParams.convert, fields, importedObjects, funSigs, directSupertypes.map(fakeCtx.mkTypeShape))
            ctxBuilder.saveSignature(sig, df.getPosition)
          case df: DatatypeDef =>
            datatypeDefs.addOne(df)
          case StructDef(id, typeParams, fields, directSupertypes) =>
            val stableFields = mutable.LinkedHashMap.empty[FunOrVarId, StableField]
            val constrParamsCtx = LocalValuesContext(fakeThis, globalValuesContext)
            fields.foreach {
              case SimpleParam(paramId, paramTypeTree) =>
                val fieldValue = valuesGen.newParam(id, ConstructorFunId, paramId)
                stableFields(paramId) = StableField(constrParamsCtx.mkType(paramTypeTree), fieldValue)
                constrParamsCtx(paramId) = fieldValue
            }
            val sig = StructSignature(id, typeParams.convert, stableFields, directSupertypes)
            ctxBuilder.saveSignature(sig, df.getPosition)
            for (superT <- directSupertypes){
              datatypeSubtypes.getOrElseUpdate(superT, mutable.LinkedHashSet.empty).addOne(id)
            }
          case df@TypeAliasDef(typeName, typeParams, params, rhs) =>
            val typeAliasParams = mutable.LinkedHashMap.empty[FunOrVarId, (Type, Value)]
            params.foreach {
              case SimpleParam(paramId, paramTypeTree) => ???
            }
            val sig = TypeAliasSignature(typeName, typeParams.convert, typeAliasParams)
            ctxBuilder.saveSignature(sig, df.getPosition)
        }
        for (df@DatatypeDef(id, typeParams, directSupertypes) <- datatypeDefs){
          val sig = DatatypeSignature(id, typeParams.convert, directSupertypes, datatypeSubtypes.getOrElse(id, mutable.LinkedHashSet.empty))
          ctxBuilder.saveSignature(sig, df.getPosition)
        }
      }
    }
    (input, ctxBuilder.build())
  }

  private def collectFunctions(functionsProvider: EncapsulatedTypeDefTree, globalValsCtx: GlobalValuesContext): Map[FunOrVarId, FunctionSignature] = {
    val funSigs = mutable.Map.empty[FunOrVarId, FunctionSignature]
    for (func <- functionsProvider.functions) {
      if (funSigs.contains(func.id)) {
        er.push(Err(ContextCreation, s"a function named ${func.id} has already been declared in ${functionsProvider.description}", functionsProvider.getPosition))
      } else {
        val paramsInclThis = mutable.LinkedHashMap.empty[Value, Type]
        val thisVal = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, ThisId)
        val localValsCtx = LocalValuesContext(thisVal, globalValsCtx)
        for (paramTree <- func.params) {
          val paramValue = globalValsCtx.valuesGen.newParam(functionsProvider.id, func.id, paramTree.paramId)
          paramsInclThis(paramValue) = localValsCtx.mkType(paramTree.paramTypeTree)
          localValsCtx(paramTree.paramId) = paramValue
        }
        val retType = func.optRetType match {
          case Some(retTypeTree) => localValsCtx.mkType(retTypeTree)
          case None => PrimitiveTypeShape.VoidType.toType
        }
        funSigs(func.id) = FunctionSignature(func.id, func.typeParams, paramsInclThis, retType, func.visibility)
      }
    }
    funSigs.toMap
  }
  
  extension(typeParams: List[TypeParam]) private def convert: List[(TypeIdentifier, Variance)] = typeParams.map {
    case TypeParam(id, variance) => (id, variance)
  }

}
