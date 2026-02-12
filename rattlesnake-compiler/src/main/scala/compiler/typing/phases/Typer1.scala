package compiler.typing.phases

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.lang.*
import compiler.lang.Field.*
import compiler.lang.Formulas.*
import compiler.lang.Formulas.SelectedField.{ResolvedField, UnresolvedField}
import compiler.lang.Operators.OperatorSignature
import compiler.lang.Types.*
import compiler.lang.Visibility.Private
import compiler.pipeline.CompilationStep.TypeChecking
import compiler.pipeline.{CompilationStep, CompilerStep}
import compiler.program.Program
import compiler.reporting.Errors.{Err, ErrorReporter, Warning}
import compiler.reporting.Position
import compiler.typing.smartcasting.ControlFlowInfo.TypeInfo
import compiler.typing.TypeStore
import compiler.typing.smartcasting.ControlFlowInfo
import compiler.util.{Result, mapVals}

import scala.collection.mutable
import scala.util.boundary


final class Typer1 extends CompilerStep[Program, (Program, TypeStore)] {

  override def apply(inProgram: Program): (Program, TypeStore) = {
    val ts = new TypeStore
    val outProgram = Program(
      inProgram.globalValuesContext,
      inProgram.interfaces.mapVals {
        case InterfaceSignature(id, typeParams, functions, directSupertypes, declPosOpt) =>
          InterfaceSignature(id, typeParams.map(typeTypeTypeParam), functions.mapVals(typeFunSig), directSupertypes.map(typeNamedType), declPosOpt)
      },
      inProgram.classes.mapVals {
        case ClassSignature(id, typeParams, fields, importedObjects, functions, directSupertypes, declPosOpt) =>
          ClassSignature(id, typeParams.map(typeTypeTypeParam), fields.mapVals(typeField), importedObjects, functions.mapVals(typeFunSig), directSupertypes.map(typeNamedType), declPosOpt)
      },
      inProgram.objects.mapVals {
        case ObjectSignature(id, importedObjects, functions, directSupertypes, declPosOpt) =>
          ObjectSignature(id, importedObjects, functions.mapVals(typeFunSig), directSupertypes.map(typeNamedType), declPosOpt)
      },
      inProgram.datatypes.mapVals {
        case DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, declPosOpt) =>
          DatatypeSignature(id, typeParams.map(typeTypeTypeParam), directSupertypes.map(typeNamedType), directSubtypes, declPosOpt)
      },
      inProgram.records.mapVals {
        case RecordSignature(id, typeParams, fields, directSupertypes, declPosOpt) =>
          RecordSignature(id, typeParams.map(typeTypeTypeParam), fields.mapVals(typeStableField), directSupertypes.map(typeNamedType), declPosOpt)
      },
      inProgram.typeAliases.mapVals {
        case TypeAliasSignature(id, typeParams, itValue, params, rhs, declPosOpt) =>
          TypeAliasSignature(id, typeParams.map(typeTypeTypeParam), itValue, params.mapVals((tpe, idVal) => (typeType(tpe), idVal)), typeType(rhs), declPosOpt)
      },
      inProgram.functions.mapVals(typeFunction)
    )
    (outProgram, ts)
  }

  private def typeFunction(function: Function): Function = {
    val Function(signature, bodyOpt, posOpt) = function
    // TODO maybe cache signature conversion
    Function(typeFunSig(signature), bodyOpt.map { bodyUntyped =>
      val (bodyTyped, _) = typeInstructions(bodyUntyped, ControlFlowInfo.empty)
      bodyTyped
    }, posOpt)
  }

  private def typeInstructions(untypedInstructions: List[Instr], cfIn: ControlFlowInfo): (List[Instr], ControlFlowInfo) = {
    var cf = cfIn
    val typedInstructionsB = List.newBuilder[Instr]
    for (untypedInstr <- untypedInstructions) {
      val (typedInstr, newCf) = typeInstr(untypedInstr, cf)
      cf = newCf
      typedInstructionsB.addOne(typedInstr)
    }
    (typedInstructionsB.result(), cf)
  }

  private def typeInstr(instr: Instr, cfIn: ControlFlowInfo): (Instr, ControlFlowInfo) = instr match {
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

  private def typeFormula(formula: Formula, cfIn: ControlFlowInfo): (TypedFormula, ControlFlowInfo) = formula match {
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

  private def typeType(tpe: Type): Type = tpe match {
    case primitiveType: PrimitiveType => primitiveType
    case namedType: NamedType => typeNamedType(namedType)
    case ClosureType(params, result) =>
      ClosureType(params.map(typeType), typeType(result))
    case tv: TypeVariable => tv
    case UnionType(types) => UnionType(types.map(typeType))
    case IntersectionType(types) => IntersectionType(types.map(typeType))
    case IntRangeType(untypedLowerBoundOpt, untypedUpperBoundOpt) =>
      val typedLowerBoundOpt = untypedLowerBoundOpt.map(typeFormula(_, ControlFlowInfo.empty)._1)
      val typedUpperBoundOpt = untypedUpperBoundOpt.map(typeFormula(_, ControlFlowInfo.empty)._1)
      IntRangeType(typedLowerBoundOpt, typedUpperBoundOpt)
  }

  private def typeNamedType(namedType: NamedType): NamedType = {
    val NamedType(typeName, typeArgs, args) = namedType
    NamedType(typeName, typeArgs.map(typeType), args.map(typeFormula(_, ControlFlowInfo.empty)._1))
  }

  private def typeField(field: Field): Field = field match {
    case ReassignableField(id, tpe) => ReassignableField(id, typeType(tpe))
    case field: StableField => typeStableField(field)
  }

  private def typeStableField(field: StableField): StableField = {
    val StableField(id, tpe, value) = field
    StableField(id, typeType(tpe), value)
  }

  private def typeTypeTypeParam(typeTypeParamInfo: TypeTypeParamInfo): TypeTypeParamInfo = {
    val TypeTypeParamInfo(tid, variance, upperBoundOpt, lowerBoundOpt) = typeTypeParamInfo
    TypeTypeParamInfo(tid, variance, upperBoundOpt.map(typeType), lowerBoundOpt.map(typeType))
  }

  private def typeFunTypeParam(functionTypeParamInfo: FunctionTypeParamInfo): FunctionTypeParamInfo = {
    val FunctionTypeParamInfo(tid, upperBoundOpt, lowerBoundOpt) = functionTypeParamInfo
    FunctionTypeParamInfo(tid, upperBoundOpt.map(typeType), lowerBoundOpt.map(typeType))
  }

  private def typeFunSig(functionSignature: FunctionSignature): FunctionSignature = {
    val FunctionSignature(ownerName, functionName, typeParams, paramsInclThis, retType, visibility, declPosOpt) = functionSignature
    FunctionSignature(ownerName, functionName, typeParams.map(typeFunTypeParam), paramsInclThis.mapVals(typeType), typeType(retType), visibility, declPosOpt)
  }

  private def isPure(typedFormula: Formula): Boolean = typedFormula match {
    case value: Value => true
    case binOp: BinOp => isPure(binOp.lhs) && isPure(binOp.rhs)
    case unaryOp: UnaryOp => isPure(unaryOp.operand)
    // TODO see if we can do something if the call target is resolved
    case Call(receiver, callTarget, typeArgs, args) => false
    case ClosureInvocation(closure, args) => false
    case Select(owner, ResolvedField(ownerSig, field)) =>
      isPure(owner) && field.isStable
    case Select(owner, UnresolvedField(fieldId)) => false
    case HasType(formula, tpe) => isPure(formula)
    case typed: TypedFormula => isPure(typed.formula)
  }

}
