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
                  (using subtypingCtx: SubtypingContext): Unit = {
    val Function(ownerId, funId, bodyOpt) = function
    val funSig = resolutionCtx.resolveFunSig(ownerId, funId).forceGetFunSig

    given TypeParamsContext = ownerTypeParamsCtx.extendedWith(funSig.typeParams)

    bodyOpt.foreach { body =>
      typeInstructions(body, ControlFlowInfo.emptyEnabled(subtypingCtx))
    }
  }

  def typeInstructions(scope: Scope, cfIn: ControlFlowInfo)
                      (using typeParamsCtx: TypeParamsContext): ControlFlowInfo = {
    var cf = cfIn
    val typedInstructionsB = List.newBuilder[Instr]
    for (untypedInstr <- scope.instructions) {
      cf = typeInstr(untypedInstr, cf)
    }
    cf
  }

  def typeInstr(instr: Instr, cfIn: ControlFlowInfo)
               (using typeParamsCtx: TypeParamsContext): ControlFlowInfo = instr match {
    case Loop(cond, condVal, body, variables) => ???
    case Disjunction(condVal, thenBr, elseBr, variables) => ???
    case StaticTypeAssert(value, tpe) => ???
    case StaticAssert(value) => ???
    case instr: AssigningInstr => ???
    case FieldWrite(owner, field, rhs) => ???
    case Return(retVal) => ???
    case Panic(msg) => ???
    case Cast(inValue, target) => ???
    case Drop(droppedValue) => ???
    case LocalDecl(localId, tpe) => ???
    case scope: Scope => ???
  }

  def typeFormula(formula: Formula)
                 (using typeParamsCtx: TypeParamsContext): ControlFlowInfo = formula match {
    case value: IdValue => ???
    case IntConst(value) => ???
    case BoolConst(value) => ???
    case StringConst(value) => ???
    case Select(owner, field) => ???
    case Sum(terms) => ???
    case Neg(operand) => ???
    case Times(terms) => ???
    case DivBy(lhs, rhs) => ???
    case Modulo(lhs, rhs) => ???
  }

  def dealiasAndTypeType(tpe: Type, ambientVarianceOpt: Option[Variance], posOpt: Option[Position])
                        (using tParamsCtx: TypeParamsContext): Unit = dealiasingCtx.dealiasType(tpe) match {
    case primitiveType: PrimitiveType => ()
    case namedType: NamedType => typeNamedTypeDealiased(namedType, ambientVarianceOpt, posOpt)
    case ClosureType(paramTypes, resultType) =>
      for paramType <- paramTypes do {
        dealiasAndTypeType(paramType, ambientVarianceOpt.map(_ * Contravariant), posOpt)
      }
      dealiasAndTypeType(resultType, ambientVarianceOpt.map(_ * Covariant), posOpt)
    case tv: TypeVariable => ()
    case UnionType(types) =>
      for tpe <- types do {
        dealiasAndTypeType(tpe, ambientVarianceOpt, posOpt)
      }
    case IntersectionType(types) =>
      for tpe <- types do {
        dealiasAndTypeType(tpe, ambientVarianceOpt, posOpt)
      }
    case IntRangeType(untypedLowerBoundOpt, untypedUpperBoundOpt) =>
      untypedLowerBoundOpt.foreach { typeFormula(_) }
      untypedUpperBoundOpt.foreach { typeFormula(_) }
  }

  def typeNamedTypeDealiased(namedType: NamedType, ambientVarianceOpt: Option[Variance], posOpt: Option[Position])
                            (using typeParamsCtx: TypeParamsContext): Unit = {
    val NamedType(typeName, typeArgs, args) = namedType
    if (args.nonEmpty) {
      er.reportError(s"unexpected value arguments for type $typeName", posOpt)
    }
    typeParamsCtx.resolve(typeName) match {
      case Some(tpInfo) =>
        if (typeArgs.nonEmpty) {
          er.reportError(s"$typeName is a type variable, hence it cannot take type arguments", posOpt)
        }
      case None => resolutionCtx.resolveTypeSig(typeName) match {
        case Some(sig) =>
          typeTypeArgsList(typeName, sig.typeParams, typeArgs, ambientVarianceOpt, posOpt)
          typeArgsList(typeName, sig.params.size, args, posOpt)
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
      }
    }
  }

  def typeField(field: Field, posOpt: Option[Position])(using typeParamsCtx: TypeParamsContext): Unit = field match {
    case ReassignableField(id, tpe) => dealiasAndTypeType(tpe, Some(Invariant), posOpt)
    case field: StableField => typeStableField(field, posOpt)
  }

  def typeStableField(field: StableField, posOpt: Option[Position])
                     (using typeParamsCtx: TypeParamsContext): Unit = {
    val StableField(id, tpe, value) = field
    dealiasAndTypeType(tpe, Some(Covariant), posOpt)
  }

  // TODO merge with typeFunTypeParam?
  def typeTypeTypeParam(typeTypeParamInfo: TypeTypeParamInfo, posOpt: Option[Position])
                       (using typeParamsCtx: TypeParamsContext): Unit = {
    val TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt) = typeTypeParamInfo
    upperBoundOpt.foreach { dealiasAndTypeType(_, None, posOpt) }
    lowerBoundOpt.foreach { dealiasAndTypeType(_, None, posOpt) }
  }

  def typeFunTypeParam(functionTypeParamInfo: FunctionTypeParamInfo, posOpt: Option[Position])
                      (using typeParamsCtx: TypeParamsContext): Unit = {
    val FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt) = functionTypeParamInfo
    upperBoundOpt.foreach { dealiasAndTypeType(_, None, posOpt) }
    lowerBoundOpt.foreach { dealiasAndTypeType(_, None, posOpt) }
  }

  def typeFunSig(functionSignature: FunctionSignature)(using typeParamsCtx: TypeParamsContext): Unit = {
    val FunctionSignature(ownerName, functionName, typeParams,
      paramsInclThis, retType, visibility, declPosOpt) = functionSignature
    for typeParam <- typeParams do {
      typeFunTypeParam(typeParam, functionSignature.declPosOpt)
    }
    for (paramId, paramType) <- paramsInclThis do {
      dealiasAndTypeType(paramType, Some(Contravariant), functionSignature.declPosOpt)
    }
    dealiasAndTypeType(retType, Some(Covariant), functionSignature.declPosOpt)
  }

  def typeInterfaceSig(interfaceSig: InterfaceSignature): Unit = {
    val InterfaceSignature(id, typeParams, functions, directSupertypes, declPosOpt) = interfaceSig

    given TypeParamsContext = TypeParamsContext(typeParams)
    
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypesAsInterfaces(interfaceSig, resolutionCtx)
  }

  def typeClassSig(classSig: ClassSignature): Unit = {
    val ClassSignature(id, typeParams, fields, functions, directSupertypes, declPosOpt) = classSig

    given TypeParamsContext = TypeParamsContext(typeParams)
    
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for tp <- typeParams do {
      typeTypeTypeParam(tp, declPosOpt)
    }
    for (_, fld) <- fields do {
      typeField(fld, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypesAsInterfaces(classSig, resolutionCtx)
  }

  def typeObjectSig(objSig: ObjectSignature): Unit = {
    val ObjectSignature(id, functions, directSupertypes, declPosOpt) = objSig

    given TypeParamsContext = TypeParamsContext.empty
    
    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypes(objSig, "interface", resolutionCtx)
  }

  def typeDatatypeSig(datatypeSig: DatatypeSignature): Unit = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, declPosOpt) = datatypeSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    typeSupertypesAsDatatypes(datatypeSig, resolutionCtx)
  }

  def typeRecordSig(recordSig: RecordSignature): Unit = {
    val RecordSignature(id, typeParams, fields, directSupertypes, declPosOpt) = recordSig
    
    given TypeParamsContext = TypeParamsContext(typeParams)
    
    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for (_, fld) <- fields do {
      typeStableField(fld, declPosOpt)
    }
    typeSupertypesAsDatatypes(recordSig, resolutionCtx)
  }

  private def checkTypeParamsAreDistinct(typeParams: Iterable[TypeParamInfo], posOpt: Option[Position]): Unit = {
    val prevNames = mutable.Set.empty[TypeIdentifier]
    for (tParam <- typeParams) {
      if (!prevNames.add(tParam.tid)) {
        er.reportError(s"duplicate type parameter: ${tParam.tid}", posOpt)
      }
    }
  }

  private def typeSupertypesAsInterfaces(sig: EncapsulatedTypeSig, resolutionCtx: ResolutionContext): Unit =
    typeSupertypes[InterfaceSignature](sig, "interface", resolutionCtx)

  private def typeSupertypesAsDatatypes(sig: UnencapsulatedTypeSig, resolutionCtx: ResolutionContext): Unit =
    typeSupertypes[DatatypeSignature](sig, "datatype", resolutionCtx)

  private def typeSupertypes[S <: AbstractTypeSig : ClassTag](sig: RuntimeTypeSignature, superTKindDescr: String, resolutionCtx: ResolutionContext): Unit = {
    for (superT <- sig.directSupertypes) {
      dealiasingCtx.dealiasType(superT) match {
        case namedType: NamedType =>
          if (resolutionCtx.resolveTypeSigAs[S](superT.typeName).isEmpty) {
            er.reportError(s"$superTKindDescr not found: ${superT.typeName}", sig.declPosOpt)
          }
        case dealiasedSuperT =>
          er.reportError(s"type $superT expands to $dealiasedSuperT, which cannot be a supertype of ${sig.id}", sig.declPosOpt)
      }
    }
  }

  private def checkSupertypesOfUnencapsulated(sig: UnencapsulatedTypeSig, resolutionCtx: ResolutionContext): Unit = {
    for (superT <- sig.directSupertypes) {
      if (resolutionCtx.resolveTypeSigAs[DatatypeSignature](superT.typeName).isEmpty) {
        er.reportError(s"datatype not found: ${superT.typeName}", sig.declPosOpt)
      }
    }
  }

  private def typeTypeArgsList(tid: TypeIdentifier, tParams: List[TypeParamInfo], tArgs: List[Type], ambientVarianceOpt: Option[Variance], posOpt: Option[Position])
                              (using TypeParamsContext): Unit = {
    if (tParams.size != tArgs.size) {
      er.reportError(s"wrong number of type parameters for $tid: expected ${tParams.size}, was ${tArgs.size}", posOpt)
    }
    val tInfosIter = tParams.iterator
    for (tArg <- tArgs) {
      val nestedAmbientVariance = tInfosIter.nextOption().flatMap(expVariance(ambientVarianceOpt, _))
      dealiasAndTypeType(tArg, nestedAmbientVariance, posOpt)
    }
  }

  // TODO maybe collect params -> args mapping for dependent typing
  private def typeArgsList(tid: TypeIdentifier, expParamsCnt: Int, args: List[Formula], posOpt: Option[Position])
                          (using TypeParamsContext): Unit = {
    if (args.size == expParamsCnt) {
      er.reportError(s"wrong number of parameters for $tid: expected $expParamsCnt, was ${args.size}", posOpt)
    }
    for (arg <- args) {
      typeFormula(arg)
    }
  }

  private def expVariance(ambientVarianceOpt: Option[Variance], tParam: TypeParamInfo): Option[Variance] = (tParam, ambientVarianceOpt) match {
    case (tParam: TypeTypeParamInfo, Some(ambientVariance)) =>
      Some(tParam.variance * ambientVariance)
    case _ => None
  }

}
