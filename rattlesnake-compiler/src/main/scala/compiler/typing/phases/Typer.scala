package compiler.typing.phases

import compiler.datastructures.Graph
import compiler.identifiers.TypeIdentifier
import compiler.irs.SSA.*
import compiler.lang.*
import compiler.lang.Field.*
import compiler.lang.Formulas.*
import compiler.lang.Types.*
import compiler.lang.Variance.*
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.contexts.*
import compiler.typing.smartcasting.ControlFlowInfo
import compiler.util.{mapVals, zipCommons}

import scala.collection.mutable
import scala.reflect.ClassTag
import scala.util.boundary


final class Typer(
                   dealiasingCtx: DealiasingContext,
                   resolutionCtx: ResolutionContext,
                   typeVarsCtx: TypeVariablesContext,
                   er: ErrorReporter
                 )(using CompilationStep) {

  def typeFunction(function: Function, ownerTypeParamsCtx: TypeParamsContext)
                  (using subtypingCtx: SubtypingContext): Function = {
    val Function(ownerId, funId, bodyOpt, posOpt) = function
    val funSig = resolutionCtx.resolveFunSig(ownerId, funId).forceGetFunSig

    given TypeParamsContext = ownerTypeParamsCtx.extendedWith(funSig.typeParams)

    Function(ownerId, funId, bodyOpt.map { bodyUntyped =>
      val (bodyTyped, _) = typeInstructions(bodyUntyped, ControlFlowInfo.emptyEnabled(subtypingCtx))
      bodyTyped
    }, posOpt)
  }

  def typeInstructions(untypedInstructions: List[Instr], cfIn: ControlFlowInfo)
                      (using typeParamsCtx: TypeParamsContext): (List[Instr], ControlFlowInfo) = {
    var cf = cfIn
    val typedInstructionsB = List.newBuilder[Instr]
    for (untypedInstr <- untypedInstructions) {
      val (typedInstr, newCf) = typeInstr(untypedInstr, cf)
      cf = newCf
      typedInstructionsB.addOne(typedInstr)
    }
    (typedInstructionsB.result(), cf)
  }

  def typeInstr(instr: Instr, cfIn: ControlFlowInfo)
               (using typeParamsCtx: TypeParamsContext): (Instr, ControlFlowInfo) = instr match {
    case Loop(untypedCond, untypedBody, variables) =>
      val (typedCond, cfAfterCond) = typeFormula(untypedCond, cfIn)
      val (typedBody, cfAfterBody) = typeInstructions(untypedBody, cfAfterCond)
      (Loop(typedCond, typedBody, variables), cfAfterCond.merged(cfAfterBody))
    case Disjunction(cond, thenBr, elseBr, variables) => ???
    case Assignment(assignedValue, rhs) => ???
    case Instantiate(assignedValue, classOrRecordName, typeArgs, initialization) => ???
    case ClosureCreation(assignedValue, params, body) => ???
    case Conversion(assignedValue, inValue, targetType) => ???
    case StaticTypeAssert(value, tpe) => ???
    case StaticAssert(formula) => ???
    case FieldWrite(owner, fieldName, rhs) => ???
    case Return(retVal) => ???
    case Panic(msg) => ???
    case Evaluate(formula) => ???
    case Cast(inValue, target) => ???
    case DynamicAssert(formula) => ???
    case LocalDecl(localId, tpe) => ???
    case ErrorInstr(instrOpt, errorMsg) =>
      throw AssertionError(s"unexpected error instruction with message \"$errorMsg\"")
  }

  def typeFormula(formula: Formula, cfIn: ControlFlowInfo)
                 (using typeParamsCtx: TypeParamsContext): (TypedFormula, ControlFlowInfo) = formula match {
    case value: IdValue => ???
    case constant: Constant => ???
    case Plus(lhs, rhs) => ???
    case Minus(lhs, rhs) => ???
    case Times(lhs, rhs) => ???
    case Div(lhs, rhs) => ???
    case Rem(lhs, rhs) => ???
    case And(lhs, rhs) => ???
    case Or(lhs, rhs) => ???
    case LessThan(lhs, rhs) => ???
    case LessOrEq(lhs, rhs) => ???
    case Equal(lhs, rhs) => ???
    case Neg(operand) => ???
    case Not(operand) => ???
    case Call(receiver, funId, typeArgs, args) => ???
    case ClosureInvocation(closure, args) => ???
    case Select(owner, fieldName) => ???
    case HasType(formula, tpe) => ???
    case typed: TypedFormula =>
      throw AssertionError(s"unexpected typed construct in first typing phase")
  }

  def typeFormulaNoCf(formula: Formula)(using typeParamsCtx: TypeParamsContext): TypedFormula =
    typeFormula(formula, ControlFlowInfo.disabled)._1

  def dealiasAndTypeType(tpe: Type, ambientVarianceOpt: Option[Variance], posOpt: Option[Position])
                        (using tParamsCtx: TypeParamsContext): Type = dealiasingCtx.dealiasType(tpe) match {
    case primitiveType: PrimitiveType => primitiveType
    case namedType: NamedType => typeNamedTypeDealiased(namedType, ambientVarianceOpt, posOpt)
    case ClosureType(params, result) =>
      ClosureType(
        params.map(dealiasAndTypeType(_, ambientVarianceOpt.map(_ * Contravariant), posOpt)),
        dealiasAndTypeType(result, ambientVarianceOpt.map(_ * Covariant), posOpt)
      )
    case tv: TypeVariable => tv
    case UnionType(types) => UnionType(types.map(dealiasAndTypeType(_, ambientVarianceOpt, posOpt)))
    case IntersectionType(types) => IntersectionType(types.map(dealiasAndTypeType(_, ambientVarianceOpt, posOpt)))
    case IntRangeType(untypedLowerBoundOpt, untypedUpperBoundOpt) =>
      val typedLowerBoundOpt = untypedLowerBoundOpt.map(typeFormulaNoCf)
      val typedUpperBoundOpt = untypedUpperBoundOpt.map(typeFormulaNoCf)
      IntRangeType(typedLowerBoundOpt, typedUpperBoundOpt)
  }

  def typeNamedTypeDealiased(namedType: NamedType, ambientVarianceOpt: Option[Variance], posOpt: Option[Position])
                            (using typeParamsCtx: TypeParamsContext): NamedType = {
    val NamedType(typeName, typeArgs, args) = namedType
    if (args.nonEmpty) {
      er.reportError(s"unexpected value arguments for type $typeName", posOpt)
    }

    def fallbackNamedType =
      NamedType(typeName, typeArgs.map(dealiasAndTypeType(_, None, posOpt)),
        typeArgsList(typeName, args.size /* avoid redundant error */ , args, ControlFlowInfo.disabled, posOpt)._1)

    typeParamsCtx.resolve(typeName) match {
      case Some(tpInfo) =>
        if (typeArgs.nonEmpty) {
          er.reportError(s"$typeName is a type variable, hence it cannot take type arguments", posOpt)
        }
        fallbackNamedType
      case None => resolutionCtx.resolveTypeSig(typeName) match {
        case Some(sig) =>
          val typedTypeArgs = typeTypeArgsList(typeName, sig.typeParams, typeArgs, ambientVarianceOpt, posOpt)
          val (typedArgs, _) = typeArgsList(typeName, sig.params.size, args, ControlFlowInfo.disabled, posOpt)
          NamedType(typeName, typedTypeArgs, typedArgs)
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
          fallbackNamedType
      }
    }
  }

  def typeField(field: Field, posOpt: Option[Position])(using typeParamsCtx: TypeParamsContext): Field = field match {
    case ReassignableField(id, tpe) => ReassignableField(id, dealiasAndTypeType(tpe, Some(Invariant), posOpt))
    case field: StableField => typeStableField(field, posOpt)
  }

  def typeStableField(field: StableField, posOpt: Option[Position])
                     (using typeParamsCtx: TypeParamsContext): StableField = {
    val StableField(id, tpe, value) = field
    StableField(id, dealiasAndTypeType(tpe, Some(Covariant), posOpt), value)
  }

  def typeTypeTypeParam(typeTypeParamInfo: TypeTypeParamInfo, posOpt: Option[Position])
                       (using typeParamsCtx: TypeParamsContext): TypeTypeParamInfo = {
    val TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt) = typeTypeParamInfo
    TypeTypeParamInfo(tid, variance,
      upperBoundOpt.map(dealiasAndTypeType(_, None, posOpt)),
      lowerBoundOpt.map(dealiasAndTypeType(_, None, posOpt))
    )
  }

  def typeFunTypeParam(functionTypeParamInfo: FunctionTypeParamInfo, posOpt: Option[Position])
                      (using typeParamsCtx: TypeParamsContext): FunctionTypeParamInfo = {
    val FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt) = functionTypeParamInfo
    FunctionTypeParamInfo(tid,
      upperBoundOpt.map(dealiasAndTypeType(_, None, posOpt)),
      lowerBoundOpt.map(dealiasAndTypeType(_, None, posOpt))
    )
  }

  def typeFunSig(functionSignature: FunctionSignature)(using typeParamsCtx: TypeParamsContext): FunctionSignature = {
    val FunctionSignature(ownerName, functionName, typeParams,
      paramsInclThis, retType, visibility, declPosOpt) = functionSignature
    FunctionSignature(ownerName, functionName, typeParams.map(typeFunTypeParam(_, functionSignature.declPosOpt)),
      paramsInclThis.mapVals(dealiasAndTypeType(_, Some(Contravariant), functionSignature.declPosOpt)),
      dealiasAndTypeType(retType, Some(Covariant), functionSignature.declPosOpt),
      visibility, declPosOpt)
  }

  def typeInterfaceSig(interfaceSig: InterfaceSignature): InterfaceSignature = {
    val InterfaceSignature(id, typeParams, functions, directSupertypes, declPosOpt) = interfaceSig

    given TypeParamsContext = TypeParamsContext(typeParams)
    
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    InterfaceSignature(id,
      typeParams.map(typeTypeTypeParam(_, declPosOpt)),
      functions.mapVals(typeFunSig),
      typeSupertypesAsInterfaces(interfaceSig, resolutionCtx),
      declPosOpt
    )
  }

  def typeClassSig(classSig: ClassSignature): ClassSignature = {
    val ClassSignature(id, typeParams, fields, functions, directSupertypes, declPosOpt) = classSig

    given TypeParamsContext = TypeParamsContext(typeParams)
    
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    ClassSignature(id,
      typeParams.map(typeTypeTypeParam(_, declPosOpt)),
      fields.mapVals(typeField(_, declPosOpt)),
      functions.mapVals(typeFunSig),
      typeSupertypesAsInterfaces(classSig, resolutionCtx),
      declPosOpt
    )
  }

  def typeObjectSig(objSig: ObjectSignature): ObjectSignature = {
    val ObjectSignature(id, functions, directSupertypes, declPosOpt) = objSig

    given TypeParamsContext = TypeParamsContext.empty
    
    ObjectSignature(id,
      functions.mapVals(typeFunSig),
      typeSupertypes(objSig, "interface", resolutionCtx),
      declPosOpt
    )
  }

  def typeDatatypeSig(datatypeSig: DatatypeSignature): DatatypeSignature = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, declPosOpt) = datatypeSig

    given TypeParamsContext = TypeParamsContext(typeParams)
    
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    DatatypeSignature(id,
      typeParams.map(typeTypeTypeParam(_, declPosOpt)),
      typeSupertypesAsDatatypes(datatypeSig, resolutionCtx),
      directSubtypes,
      declPosOpt
    )
  }

  def typeRecordSig(recordSig: RecordSignature): RecordSignature = {
    val RecordSignature(id, typeParams, fields, directSupertypes, declPosOpt) = recordSig
    
    given TypeParamsContext = TypeParamsContext(typeParams)
    
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    RecordSignature(id,
      typeParams.map(typeTypeTypeParam(_, declPosOpt)),
      fields.mapVals(typeStableField(_, declPosOpt)),
      typeSupertypesAsDatatypes(recordSig, resolutionCtx),
      declPosOpt
    )
  }

  private def checkTypeParamsAreDistinct(typeParams: Iterable[TypeParamInfo], posOpt: Option[Position]): Unit = {
    val prevNames = mutable.Set.empty[TypeIdentifier]
    for (tParam <- typeParams) {
      if (!prevNames.add(tParam.tid)) {
        er.reportError(s"duplicate type parameter: ${tParam.tid}", posOpt)
      }
    }
  }

  private def typeSupertypesAsInterfaces(sig: Encapsulated, resolutionCtx: ResolutionContext): List[NamedType] =
    typeSupertypes[InterfaceSignature](sig, "interface", resolutionCtx)

  private def typeSupertypesAsDatatypes(sig: Unencapsulated, resolutionCtx: ResolutionContext): List[NamedType] =
    typeSupertypes[DatatypeSignature](sig, "datatype", resolutionCtx)

  private def typeSupertypes[S <: Abstract : ClassTag](sig: RuntimeTypeSignature, superTKindDescr: String, resolutionCtx: ResolutionContext): List[NamedType] = {
    val typedDirectSuperTypesB = List.newBuilder[NamedType]
    for (superT <- sig.directSupertypes) {
      dealiasingCtx.dealiasType(superT) match {
        case namedType: NamedType =>
          if (resolutionCtx.resolveTypeSigAs[S](superT.typeName).isEmpty) {
            er.reportError(s"$superTKindDescr not found: ${superT.typeName}", sig.declPosOpt)
          }
          typedDirectSuperTypesB.addOne(namedType)
        case dealiasedSuperT =>
          er.reportError(s"type $superT expands to $dealiasedSuperT, which cannot be a supertype of ${sig.id}", sig.declPosOpt)
      }
    }
    typedDirectSuperTypesB.result()
  }

  private def checkSupertypesOfUnencapsulated(sig: Unencapsulated, resolutionCtx: ResolutionContext): Unit = {
    for (superT <- sig.directSupertypes) {
      if (resolutionCtx.resolveTypeSigAs[DatatypeSignature](superT.typeName).isEmpty) {
        er.reportError(s"datatype not found: ${superT.typeName}", sig.declPosOpt)
      }
    }
  }

  private def typeTypeArgsList(tid: TypeIdentifier, tParams: List[TypeParamInfo], tArgs: List[Type], ambientVarianceOpt: Option[Variance], posOpt: Option[Position])
                              (using TypeParamsContext): List[Type] = {
    if (tParams.size != tArgs.size) {
      er.reportError(s"wrong number of type parameters for $tid: expected ${tParams.size}, was ${tArgs.size}", posOpt)
    }
    val typedTArgsB = List.newBuilder[Type]
    val tInfosIter = tParams.iterator
    for (tArg <- tArgs) {
      val nestedAmbientVariance = tInfosIter.nextOption().flatMap(expVariance(ambientVarianceOpt, _))
      val typedTArg = dealiasAndTypeType(tArg, nestedAmbientVariance, posOpt)
      typedTArgsB.addOne(typedTArg)
    }
    typedTArgsB.result()
  }

  // TODO maybe collect params -> args mapping for dependent typing
  private def typeArgsList(tid: TypeIdentifier, expParamsCnt: Int, args: List[Formula], cfIn: ControlFlowInfo, posOpt: Option[Position])
                          (using TypeParamsContext): (List[TypedFormula], ControlFlowInfo) = {
    if (args.size == expParamsCnt) {
      er.reportError(s"wrong number of parameters for $tid: expected $expParamsCnt, was ${args.size}", posOpt)
    }
    var cf = cfIn
    val typedArgsB = List.newBuilder[TypedFormula]
    for (arg <- args) {
      val (typedArg, cfAfterArgEval) = typeFormula(arg, cf)
      cf = cfAfterArgEval
      typedArgsB.addOne(typedArg)
    }
    (typedArgsB.result(), cf)
  }

  private def expVariance(ambientVarianceOpt: Option[Variance], tParam: TypeParamInfo): Option[Variance] = (tParam, ambientVarianceOpt) match {
    case (tParam: TypeTypeParamInfo, Some(ambientVariance)) =>
      Some(tParam.variance * ambientVariance)
    case _ => None
  }

}
