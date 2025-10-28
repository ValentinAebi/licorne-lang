package compiler.analysisctx

import compiler.irs.Asts
import compiler.irs.Asts.{CaptureSetTree, Expr, PackageDef, Source, TypeShapeTree, TypeTree}
import compiler.pipeline.CompilationStep.ContextCreation
import compiler.pipeline.CompilerStep
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.valuesconversion.{LocalValuesContext, ValuesGenerator}
import identifiers.FunOrVarId
import lang.CaptureDescriptors.CaptureSet
import lang.Values.{And, False, Formula, IntConstant, StringConstant, True, Value}
import lang.Types.{NamedTypeShape, Type, TypeShape}
import lang.{FunctionSignature, Keyword, PackageSignature}

import scala.collection.mutable

final class ContextCreator(er: ErrorReporter) extends CompilerStep[List[Source], (List[Source], AnalysisContext)] {

  override def apply(input: List[Source]): (List[Source], AnalysisContext) = {
    val ctxBuilder = AnalysisContext.Builder(er)
//    for (src <- input; df <- src.defs) {
//      val sig = df match {
//        case Asts.PackageDef(packageName, importedPackages, functions) =>
//          
//          PackageSignature(packageName, importedPackages, )
//        case Asts.ClassDef(className, typeParams, params, functions) => ???
//        case Asts.StructDef(structName, typeParams, fields, directSupertypes, isAbstract) => ???
//        case Asts.TypeAliasDef(typeName, typeParams, params, rhs) => ???
//      }
//      ctxBuilder.saveSignature(sig, df.getPosition)
//    }
    (input, ctxBuilder.build())
  }
  
//  private def collectFunctions(classOrPkg: ClassOrPackageDefTree, valuesGen: ValuesGenerator): List[FunctionSignature] = {
//    val funSigs = mutable.Map.empty[FunOrVarId, FunctionSignature]
//    for (func <- classOrPkg.functions){
//      if (funSigs.contains(func.id)){
//        val classOrPkgStr = if classOrPkg.isInstanceOf[PackageDef] then "package" else "class"
//        er.push(Err(ContextCreation, s"a function named ${func.id} has already been declared in $classOrPkg ${func.id}", classOrPkg.getPosition))
//      } else {
//        val params = mutable.LinkedHashMap.empty[Value, Type]
//        val valuesCtx = LocalValuesContext()
//        for (paramTree <- func.params) {
//          val value = valuesGen.newParam(paramTree.paramId, classOrPkg.name, func.id)
//          params(value) = mkType(paramTree.paramTypeTree)
//          params2Values(paramTree.paramId) = value
//        }
//        funSigs(func.id) = FunctionSignature(func.id, func.typeParams, )
//      }
//    }
//  }
  
}
