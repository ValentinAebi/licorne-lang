package compiler.typing

import compiler.identifiers.TypeIdentifier
import compiler.irs.SSA.*
import compiler.irs.Tokens.BoolLitToken
import compiler.lang.*
import compiler.lang.Field.*
import compiler.lang.Formulas.*
import compiler.lang.Types.*
import compiler.lang.Types.PrimitiveType.{BoolType, DoubleType, StringType}
import compiler.lang.Variance.*
import compiler.pipeline.CompilationStep
import compiler.reporting.Errors.ErrorReporter
import compiler.reporting.Position
import compiler.typing.contexts.*

import scala.collection.mutable
import scala.reflect.ClassTag


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
      typeInstructions(body.instructions, body)
    }
  }

  def typeInstructions(instructions: Iterable[Instr], currScope: Scope)
                      (using typeParamsCtx: TypeParamsContext): Unit = {
    for (untypedInstr <- instructions) {
      typeInstr(untypedInstr, currScope)
    }
  }

  def typeInstr(instr: Instr, currScope: Scope)
               (using typeParamsCtx: TypeParamsContext): Unit = instr match {
    case Loop(condScope, condVal, body, variables) => ???
    case Disjunction(condVal, thenBr, elseBr, variables) => ???
    case StaticTypeAssert(value, tpe) => ???
    case StaticAssert(value) => ???
    case AssignVal(assigned, src) => ???
    case AssignIntConst(assigned, src) => ???
    case AssignBoolConst(assigned, src) => ???
    case AssignStringConst(assigned, src) => ???
    case NumNeg(assigned, operand) => ???
    case Add(assigned, lhs, rhs) => ???
    case Sub(assigned, lhs, rhs) => ???
    case Mul(assigned, lhs, rhs) => ???
    case Div(assigned, lhs, rhs) => ???
    case Rem(assigned, lhs, rhs) => ???
    case LogicNeg(assigned, operand) => ???
    case And(assigned, lhs, rhs) => ???
    case Or(assigned, lhs, rhs) => ???
    case Equal(assigned, lhs, rhs) => ???
    case Leq(assigned, lhs, rhs) => ???
    case Lt(assigned, lhs, rhs) => ???
    case FieldRead(assigned, owner, field) => ???
    case InvokeFunc(assigned, receiver, func, typeArgs, args) => ???
    case InvokeClosure(assigned, callee, args) => ???
    case Instantiate(assigned, classOrRecordName, typeArgs) => ???
    case MkClosure(assigned, params, body) => ???
    case TypeTest(assigned, testedValue, testedTypeId) => ???
    case Conversion(assigned, inValue, targetType) => ???
    case FieldWrite(owner, field, rhs) => ???
    case Return(retVal) => ???
    case Panic(msg) => ???
    case Cast(inValue, target) => ???
    case Drop(droppedValue) => ???
    case LocalDecl(localId, tpe) => ???
    case scope: Scope =>
      assert(scope.outScopeOpt.contains(currScope))
      typeInstructions(scope.instructions, scope)
  }

  def typeFormula(formula: Formula, scope: Scope, posOpt: Option[Position])
                 (using typeParamsCtx: TypeParamsContext): Type = formula match {
      case value: IdValue => scope.typeOf(value)
      case IntConst(value) => IntRangeType.singleton(IntConst(value))
      case BoolConst(value) => BoolType
      case StringConst(value) => StringType
      case sel@Select(owner, FieldResolutionTarget.Resolved(_, _, instantiatedFieldType)) =>
        scope.smartcastFor(sel).getOrElse(instantiatedFieldType)
      case sel@Select(owner, FieldResolutionTarget.Unresolved(fieldId)) =>
        val ownerType = typeFormula(owner, scope, posOpt)
        val (resolvedField, tpe) = resolutionCtx.resolveFieldAccess(ownerType, fieldId, posOpt)
        sel.field = resolvedField
        scope.smartcastFor(sel).getOrElse(tpe)
      case Call(receiver, InvocationTarget.Resolved(ownerSig, funSig, instantiatedReturnType), args) => instantiatedReturnType
      case call@Call(receiver, InvocationTarget.Unresolved(funId), args) =>
        val receiverType = typeFormula(receiver, scope, posOpt)
        val (invocationTarget, retType) = resolutionCtx.resolveFunSig(receiverType, funId, posOpt)
        call.func = invocationTarget
        retType
      case Plus(lhs, rhs) => ???
      case Neg(operand) => ???
      case Times(lhs, rhs) => ???
      case DivBy(lhs, rhs) => ???
      case Modulo(lhs, rhs) => ???
    }

  def dealiasAndTypeType(tpe: Type, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                        (using tParamsCtx: TypeParamsContext): Unit = dealiasingCtx.dealiasType(tpe) match {
    case primitiveType: PrimitiveType => ()
    case namedType: NamedType => typeNamedTypeDealiased(namedType, ambientVarianceOpt, currScope, posOpt)
    case ClosureType(paramTypes, resultType) =>
      for paramType <- paramTypes do {
        dealiasAndTypeType(paramType, ambientVarianceOpt.map(_ * Contravariant), currScope, posOpt)
      }
      dealiasAndTypeType(resultType, ambientVarianceOpt.map(_ * Covariant), currScope, posOpt)
    case tv: TypeVariable => ()
    case UnionType(types) =>
      for tpe <- types do {
        dealiasAndTypeType(tpe, ambientVarianceOpt, currScope, posOpt)
      }
    case IntersectionType(types) =>
      for tpe <- types do {
        dealiasAndTypeType(tpe, ambientVarianceOpt, currScope, posOpt)
      }
    case IntRangeType(untypedLowerBoundOpt, untypedUpperBoundOpt) =>
      untypedLowerBoundOpt.foreach {
        typeFormula(_, currScope, posOpt)
      }
      untypedUpperBoundOpt.foreach {
        typeFormula(_, currScope, posOpt)
      }
  }

  def typeNamedTypeDealiased(namedType: NamedType, ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
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
          typeTypeArgsList(typeName, sig.typeParams, typeArgs, ambientVarianceOpt, currScope, posOpt)
          typeArgsList(typeName, sig.params.size, args, currScope, posOpt)
        case None =>
          er.reportError(s"type not found: $typeName", posOpt)
      }
    }
  }

  def typeField(field: Field, currScope: Scope, posOpt: Option[Position])(using typeParamsCtx: TypeParamsContext): Unit = field match {
    case ReassignableField(id, tpe) => dealiasAndTypeType(tpe, Some(Invariant), currScope, posOpt)
    case field: StableField => typeStableField(field, currScope, posOpt)
  }

  def typeStableField(field: StableField, currScope: Scope, posOpt: Option[Position])
                     (using typeParamsCtx: TypeParamsContext): Unit = {
    val StableField(id, tpe, value) = field
    dealiasAndTypeType(tpe, Some(Covariant), currScope, posOpt)
  }

  // TODO merge with typeFunTypeParam?
  def typeTypeTypeParam(typeTypeParamInfo: TypeTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                       (using typeParamsCtx: TypeParamsContext): Unit = {
    val TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt) = typeTypeParamInfo
    upperBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
    lowerBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
  }

  def typeFunTypeParam(functionTypeParamInfo: FunctionTypeParamInfo, currScope: Scope, posOpt: Option[Position])
                      (using typeParamsCtx: TypeParamsContext): Unit = {
    val FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt) = functionTypeParamInfo
    upperBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
    lowerBoundOpt.foreach {
      dealiasAndTypeType(_, None, currScope, posOpt)
    }
  }

  def typeFunSig(functionSignature: FunctionSignature)(using typeParamsCtx: TypeParamsContext): Unit = {
    val FunctionSignature(ownerName, functionName, typeParams,
      paramsInclThis, retType, sigScope, visibility, declPosOpt) = functionSignature
    for typeParam <- typeParams do {
      typeFunTypeParam(typeParam, functionSignature.sigScope, functionSignature.declPosOpt)
    }
    for (paramId, paramType) <- paramsInclThis do {
      dealiasAndTypeType(paramType, Some(Contravariant), functionSignature.sigScope, functionSignature.declPosOpt)
    }
    dealiasAndTypeType(retType, Some(Covariant), functionSignature.sigScope, functionSignature.declPosOpt)
  }

  def typeInterfaceSig(interfaceSig: InterfaceSignature): Unit = {
    val InterfaceSignature(id, typeParams, functions, directSupertypes, sigScope, declPosOpt) = interfaceSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, sigScope, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypesAsInterfaces(interfaceSig, resolutionCtx)
  }

  def typeClassSig(classSig: ClassSignature): Unit = {
    val ClassSignature(id, typeParams, fields, functions, directSupertypes, sigScope, declPosOpt) = classSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for tp <- typeParams do {
      typeTypeTypeParam(tp, sigScope, declPosOpt)
    }
    for (_, fld) <- fields do {
      typeField(fld, sigScope, declPosOpt)
    }
    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypesAsInterfaces(classSig, resolutionCtx)
  }

  def typeObjectSig(objSig: ObjectSignature): Unit = {
    val ObjectSignature(id, functions, directSupertypes, sigScope, declPosOpt) = objSig

    given TypeParamsContext = TypeParamsContext.empty

    for (_, funSig) <- functions do {
      typeFunSig(funSig)
    }
    typeSupertypes(objSig, "interface", resolutionCtx)
  }

  def typeDatatypeSig(datatypeSig: DatatypeSignature): Unit = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, sigScope, declPosOpt) = datatypeSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, sigScope, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    typeSupertypesAsDatatypes(datatypeSig, resolutionCtx)
  }

  def typeRecordSig(recordSig: RecordSignature): Unit = {
    val RecordSignature(id, typeParams, fields, directSupertypes, sigScope, declPosOpt) = recordSig

    given TypeParamsContext = TypeParamsContext(typeParams)

    for typeParam <- typeParams do {
      typeTypeTypeParam(typeParam, sigScope, declPosOpt)
    }
    checkTypeParamsAreDistinct(typeParams, declPosOpt)
    for (_, fld) <- fields do {
      typeStableField(fld, sigScope, declPosOpt)
    }
    typeSupertypesAsDatatypes(recordSig, resolutionCtx)
  }
  
  private def saveType(idValue: IdValue, tpe: Type): Unit = {
    idValue.definingScope.saveType(idValue, tpe)
  }
  
  private def saveSmartcast(idValue: IdValue, tpe: Type, scope: Scope): Unit = {
    scope.saveType(idValue, tpe)
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

  private def typeTypeArgsList(tid: TypeIdentifier, tParams: List[TypeParamInfo], tArgs: List[Type], ambientVarianceOpt: Option[Variance], currScope: Scope, posOpt: Option[Position])
                              (using TypeParamsContext): Unit = {
    if (tParams.size != tArgs.size) {
      er.reportError(s"wrong number of type parameters for $tid: expected ${tParams.size}, was ${tArgs.size}", posOpt)
    }
    val tInfosIter = tParams.iterator
    for (tArg <- tArgs) {
      val nestedAmbientVariance = tInfosIter.nextOption().flatMap(expVariance(ambientVarianceOpt, _))
      dealiasAndTypeType(tArg, nestedAmbientVariance, currScope, posOpt)
    }
  }

  // TODO maybe collect params -> args mapping for dependent typing
  private def typeArgsList(tid: TypeIdentifier, expParamsCnt: Int, args: List[Formula], currScope: Scope, posOpt: Option[Position])
                          (using TypeParamsContext): Unit = {
    if (args.size == expParamsCnt) {
      er.reportError(s"wrong number of parameters for $tid: expected $expParamsCnt, was ${args.size}", posOpt)
    }
    for (arg <- args) {
      typeFormula(arg, currScope, posOpt)
    }
  }

  private def expVariance(ambientVarianceOpt: Option[Variance], tParam: TypeParamInfo): Option[Variance] = (tParam, ambientVarianceOpt) match {
    case (tParam: TypeTypeParamInfo, Some(ambientVariance)) =>
      Some(tParam.variance * ambientVariance)
    case _ => None
  }

}
