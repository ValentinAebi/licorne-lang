package compiler.typing.phases

import compiler.identifiers.TypeIdentifier
import compiler.irs.ssa.Formulas.IdValue
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{EncapsulatedTypeSig, FunctionSignature, InterfaceSignature}
import compiler.pipeline.CompilationStep.OverridesAnalysis
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.smt.{CounterexampleBox, IntHandlingMode, Reasoning, Solver}
import compiler.typing.SubtypingInfo
import compiler.typing.contexts.SubtypingContext.SupertypesSubst
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext}
import compiler.valproxies.ProxyStore
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.mutable

final class OverridesChecker(
                              ihm: IntHandlingMode[?],
                              proxyStore: ProxyStore,
                              er: ErrorReporter,
                              counterExBoxOpt: Option[CounterexampleBox],
                              continueIfErrors: Boolean = false
                            ) extends CompilerStep[(Program, SubtypingInfo), (Program, SubtypingInfo)] {

  private given CompilationStep = OverridesAnalysis

  override def apply(input: (Program, SubtypingInfo)): (Program, SubtypingInfo) = {
    val (program, SubtypingInfo(subtypingGraph, flattenedSubtypingMaps)) = input
    
    given globalValsCtx: GlobalValuesContext = program.globalValuesContext

    val dealiasingCtx = DealiasingContext(program.typeAliases)
    Reasoning.usingFreshSolver(ihm, dealiasingCtx, globalValsCtx, proxyStore, counterExBoxOpt) { solver =>
      val resolutionCtx = ResolutionContext(program, er)
      val subtypingCtx = SubtypingContext(subtypingGraph, flattenedSubtypingMaps, dealiasingCtx, resolutionCtx, solver, proxyStore, globalValsCtx, er, counterExBoxOpt)
      analyzeOverrides(flattenedSubtypingMaps, resolutionCtx, subtypingCtx, dealiasingCtx, solver)
    }
    
    if (continueIfErrors) {
      er.displayErrors()
    } else {
      er.displayAndTerminateIfErrors()
    }

    input
  }

  private def analyzeOverrides(flattenedSupertypesSubstitutions: SupertypesSubst, resolutionCtx: ResolutionContext, subtypingCtx: SubtypingContext, dealiasingCtx: DealiasingContext, solver: Solver): Unit = {
    for {
      (subT, subTSupertypes) <- flattenedSupertypesSubstitutions
      (superT, typeTypeParamsSubst) <- subTSupertypes
    } {
      val subTSig = resolutionCtx.resolveTypeSig(subT).get
      val superTSig = resolutionCtx.resolveTypeSig(superT).get
      (subTSig, superTSig) match {
        case (subTSig: EncapsulatedTypeSig, superTSig: EncapsulatedTypeSig) =>
          for ((funId, superFunSig@FunctionSignature(_, _, superFunTypeParams, superFunParams, superFunPrecondOpt, superFunRetType, _, superFunVisibility, superFunPurity, _, superFunDeclPosOpt, isSynthetic)) <- superTSig.functions) {
            subTSig.functions.get(funId) match {
              // TODO allow method implementation in interfaces?
              case None if subTSig.isInstanceOf[InterfaceSignature] => ()
              case None =>
                er.reportError(s"$subT does not implement method $funId declared in its supertype $superT", subTSig.declPosOpt)
              case Some(subFunSig@FunctionSignature(_, _, subFunTypeParams, subFunParams, subFunPrecondOpt, subFunRetType, _, subFunVisibility, subFunPurity, _, subFunDeclPosOpt, isSynthetic)) =>
                val typeParamsLenMatch = subFunTypeParams.size == superFunTypeParams.size
                val paramsLenMatch = subFunParams.size == superFunParams.size
                if (!typeParamsLenMatch) {
                  er.reportError(s"length of type parameters list in method $funId in $subT does not match its length in its supertype $superT", subFunDeclPosOpt)
                }
                if (!paramsLenMatch) {
                  er.reportError(s"length of parameters list in method $funId in $subT does not match its length in its supertype $superT", subFunDeclPosOpt)
                }
                if (typeParamsLenMatch && paramsLenMatch) {
                  val funTypeParamsSubst = mutable.Map.empty[TypeIdentifier, Type]
                  for ((superFunTp, subFunTp) <- superFunTypeParams zip subFunTypeParams) {

                    def mkErrorMsg(upOrLow: String): String =
                      s"$upOrLow bound of type parameter ${subFunTp.tid} of function $funId in $subT does not conform to the signature of the overridden function in $superT"

                    subFunTp.upperBoundOpt.foreach { subFunUpperBound =>
                      superFunTp.upperBoundOpt match {
                        case Some(superFunUpperBound) =>
                          subtypingCtx.enforceIsSubtype(superFunUpperBound, subFunUpperBound, mkErrorMsg("upper"), subFunDeclPosOpt)
                        case None =>
                          er.reportError(mkErrorMsg("upper"), subFunDeclPosOpt)
                      }
                    }
                    subFunTp.lowerBoundOpt.foreach { subFunLowerBound =>
                      superFunTp.lowerBoundOpt match {
                        case Some(superFunLowerBound) =>
                          subtypingCtx.enforceIsSubtype(subFunLowerBound, superFunLowerBound, mkErrorMsg("lower"), subFunDeclPosOpt)
                        case None =>
                          er.reportError(mkErrorMsg("lower"), subFunDeclPosOpt)
                      }
                    }
                    funTypeParamsSubst.addOne(superFunTp.tid -> NamedType(subFunTp.tid, List.empty, List.empty))
                  }
                  val typeParamsSubst = typeTypeParamsSubst ++ funTypeParamsSubst
                  val valsSubst = mutable.Map.empty[IdValue, IdValue]
                  // TODO do not forget to check refinements on the receiver (the base type is not checked here)
                  val superTSubst = superTSig.toType(typeParamsSubst)
                  for (((subParamVal, subParamType), (superParamVal, superParamTypeRaw)) <- subFunParams.tail zip superFunParams.tail) {
                    val superParamTypeSubst = superParamTypeRaw.substitute(typeParamsSubst, valsSubst.toMap)
                    val subParamTypeErased = dealiasingCtx.eraseRefinements(subParamType)
                    val superParamTypeErased = dealiasingCtx.eraseRefinements(superParamTypeSubst)
                    if (subParamTypeErased != superParamTypeErased) {
                      er.reportError(s"type mismatch on parameter ${subParamVal.name} of method $funId: " +
                        s"erased type is $subParamTypeErased but should be $superParamTypeErased since the method overrides $funId in $superTSubst", subFunDeclPosOpt)
                    } else if (!subtypingCtx.isSubtype(superParamTypeSubst, subParamType)) {
                      er.reportError(s"type mismatch on parameter ${subParamVal.name} of method $funId: " +
                        s"declared type $subParamType is not a supertype of the type $superParamTypeSubst of the corresponding parameter in the overridden method $funId in $superT", subFunDeclPosOpt)
                    }
                    valsSubst(superParamVal) = subParamVal
                  }
                  val expectedRetType = superFunRetType.substitute(typeParamsSubst, valsSubst.toMap)
                  subtypingCtx.enforceIsSubtypeExpAct(subFunRetType, expectedRetType, s"return type of method $funId that overrides $funId in $superT", subFunDeclPosOpt)
                  val precondOverrideIsValid = subFunPrecondOpt.forall(subFunPrecond => superFunPrecondOpt.exists(superFunPrecond => solver.canProveImplication(superFunPrecond.substitute(valsSubst), subFunPrecond)))
                  if (!precondOverrideIsValid) {
                    er.reportError(s"$funId in $subT overrides $funId in $superT but I cannot prove that the precondition of the overridden method is respected", subFunDeclPosOpt)
                  }
                }
                if (!subFunVisibility.atLeastAsPermissiveAs(superFunVisibility)) {
                  er.reportError(s"$funId in $subT overrides $funId in $superT but has a more restricted visibility", subFunDeclPosOpt)
                }
                if (!subFunPurity.conformsTo(superFunPurity)) {
                  er.reportError(s"$funId in $subT overrides $funId in $superT but violates its declared purity", subFunDeclPosOpt)
                }
            }
          }
        case _ => ()
      }
    }
  }

}
