package compiler.typing.phases

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.lang.*
import compiler.lang.Formulas.IdValue
import compiler.lang.Types.{NamedType, Type}
import compiler.pipeline.CompilationStep.{DeclarationsAnalysis, SubtypingAnalysis}
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.smt.{Reasoning, Solver}
import compiler.typing.SubtypingInfo
import compiler.typing.contexts.SubtypingContext.SupertypesSubst
import compiler.typing.contexts.{DealiasingContext, ResolutionContext, SubtypingContext, TypeVariablesContext}
import compiler.valproxies.ProxyStore

import scala.collection.mutable
import scala.util.boundary

final class SubtypingChecker(
                              private val typeVarsCtx: TypeVariablesContext,
                              private val proxyStore: ProxyStore,
                              private val er: ErrorReporter
                            ) extends CompilerStep[Program, (Program, SubtypingInfo)] {

  private given CompilationStep = SubtypingAnalysis

  override def apply(program: Program): (Program, SubtypingInfo) = {
    val dealiasingCtx = DealiasingContext(program.typeAliases)
    val resolutionCtx = ResolutionContext(program, typeVarsCtx, er)
    er.displayAndTerminateIfErrors()

    val subtypingGraph = buildSubtypingGraph(program)
    checkSubtypingCyclicity(subtypingGraph, resolutionCtx)
    er.displayAndTerminateIfErrors()

    val flattenedSubtypingMaps = buildAndCheckFlattenedSubtypingMaps(subtypingGraph, resolutionCtx)
    er.displayAndTerminateIfErrors()

    Reasoning.usingFreshSolver { solver =>
      val subtypingCtx = SubtypingContext(subtypingGraph, flattenedSubtypingMaps, dealiasingCtx, resolutionCtx, solver, proxyStore, er)
      analyzeOverrides(flattenedSubtypingMaps, resolutionCtx, subtypingCtx)
    }
    er.displayAndTerminateIfErrors()

    (program, SubtypingInfo(subtypingGraph, flattenedSubtypingMaps))
  }

  private def buildSubtypingGraph(program: Program): Graph[TypeIdentifier] = {
    val graphB = Graph.Builder[TypeIdentifier]()
    for (sig <- program.runtimeSignatures) {
      val id = sig.id
      graphB.addVertex(id)
      graphB.addDescendants(id, sig.directSupertypes.map(_.typeName))
    }
    graphB.build()
  }

  private def checkSubtypingCyclicity(subtypingGraph: Graph[TypeIdentifier], resolutionCtx: ResolutionContext): Unit = {
    subtypingGraph.findShortestCycle().foreach { cycle =>
      val posOpt = boundary {
        for (tid <- cycle) {
          resolutionCtx.declarationPositionOf(tid).foreach { pos =>
            boundary.break(Some(pos))
          }
        }
        None
      }
      er.reportError("cyclic subtyping: " ++ cycle.mkString(" <: "), posOpt)
    }
  }

  private def buildAndCheckFlattenedSubtypingMaps(subtypingGraph: Graph[TypeIdentifier], resolutionCtx: ResolutionContext): SupertypesSubst = {
    val flattenedSupertypesSubstitutions: SupertypesSubst = mutable.SeqMap.empty

    for (subtypeId <- subtypingGraph.topologicalSort().reverse) {
      val subtypeSupertypes = mutable.LinkedHashMap.empty[TypeIdentifier, Map[TypeIdentifier, Type]]

      def checkAndSave(name: TypeIdentifier, newSubst: Map[TypeIdentifier, Type], posOpt: Option[Position]): Unit = {
        subtypeSupertypes.get(name) match {
          case Some(prevSubst) =>
            if (prevSubst != newSubst) {
              val supertype2Sig = resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](name).get
              val conflictingType1 = supertype2Sig.toType(prevSubst)
              val conflictingType2 = supertype2Sig.toType(newSubst)
              er.reportError(s"$subtypeId subtypes both $conflictingType1 and $conflictingType2", posOpt)
            }
          case None =>
            subtypeSupertypes(name) = newSubst
        }
      }

      val subtypeSig = resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](subtypeId).get
      for (supertype1 <- subtypeSig.directSupertypes) {
        val supertype1Sig = resolutionCtx.resolveTypeSigAs[RuntimeTypeSignature](supertype1.typeName).get
        val oneStepSubst = (supertype1Sig.typeParams.map(_._1) zip supertype1.typeArgs).toMap
        checkAndSave(supertype1.typeName, oneStepSubst, subtypeSig.declPosOpt)
        for ((supertype2Id, superSubst) <- flattenedSupertypesSubstitutions(supertype1.typeName)) {
          val composedSubst = for (tid, tpe) <- superSubst yield tid -> tpe.substitute(oneStepSubst, Map.empty)
          checkAndSave(supertype2Id, composedSubst, subtypeSig.declPosOpt)
        }
      }
      flattenedSupertypesSubstitutions(subtypeId) = subtypeSupertypes
    }

    flattenedSupertypesSubstitutions
  }

  private def analyzeOverrides(flattenedSupertypesSubstitutions: SupertypesSubst, resolutionCtx: ResolutionContext, subtypingCtx: SubtypingContext): Unit = {
    for ((subT, subTSupertypes) <- flattenedSupertypesSubstitutions; (superT, typeTypeParamsSubst) <- subTSupertypes) {
      val subTSig = resolutionCtx.resolveTypeSig(subT).get
      val superTSig = resolutionCtx.resolveTypeSig(superT).get
      (subTSig, superTSig) match {
        case (subTSig: EncapsulatedTypeSig, superTSig: EncapsulatedTypeSig) =>
          for ((funId, superFunSig@FunctionSignature(_, _, superFunTypeParams, superFunParams, superFunRetType, _, superFunVisibility, superFunDeclPosOpt)) <- superTSig.functions) {
            subTSig.functions.get(funId) match {
              // TODO allow method implementation in interfaces?
              case None if subTSig.isInstanceOf[InterfaceSignature] => ()
              case None =>
                er.reportError(s"$subT does not implement method $funId declared in its supertype $superT", subTSig.declPosOpt)
              case Some(subFunSig@FunctionSignature(_, _, subFunTypeParams, subFunParams, subFunRetType, _, subFunVisibility, subFunDeclPosOpt)) =>
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
                  for (((subParamVal, subParamType), (superParamVal, superParamType)) <- subFunParams.tail zip superFunParams.tail) {
                    val expectedSubParamType = superParamType.substitute(typeParamsSubst, valsSubst.toMap)
                    if (subParamType != expectedSubParamType) {
                      er.reportError(s"type mismatch on parameter ${subParamVal.name} of method $funId: " +
                        s"type is $subParamType but should be $expectedSubParamType since the method overrides $funId in $superTSubst", subFunDeclPosOpt)
                    }
                    valsSubst(superParamVal) = subParamVal
                  }
                  val expectedRetType = superFunRetType.substitute(typeParamsSubst, valsSubst.toMap)
                  subtypingCtx.enforceIsSubtypeExpAct(subFunRetType, superFunRetType, s"return type of method $funId that overrides $funId in $superT", subFunDeclPosOpt)
                }
                if (!subFunVisibility.atLeastAsPermissiveAs(superFunVisibility)) {
                  er.reportError(s"$funId in $subT overrides $funId in $superT but has a more restricted visibility", subFunDeclPosOpt)
                }
            }
          }
        case _ => ()
      }
    }
  }

}
