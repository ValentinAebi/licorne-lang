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
import compiler.typing.TypeStore
import compiler.typing.contexts.DealiasingContext
import compiler.typing.smartcasting.ControlFlowInfo
import compiler.util.{Result, mapVals}

import scala.collection.mutable
import scala.util.boundary


final class TyperPhase1 extends CompilerStep[Program, (Program, TypeStore)] {

  override def apply(inProgram: Program): (Program, TypeStore) = {
    val ts = new TypeStore
    val interfaces = inProgram.interfaces.mapVals {
      case InterfaceSignature(id, typeParams, functions, directSupertypes, declPosOpt) =>
        InterfaceSignature(id, typeParams.map(typeTypeTypeParam), functions.mapVals(typeFunSig), directSupertypes.map(typeNamedType), declPosOpt)
    }
    val classes = inProgram.classes.mapVals {
      case ClassSignature(id, typeParams, fields, importedObjects, functions, directSupertypes, declPosOpt) =>
        ClassSignature(id, typeParams.map(typeTypeTypeParam), fields.mapVals(typeField), importedObjects, functions.mapVals(typeFunSig), directSupertypes.map(typeNamedType), declPosOpt)
    }
    val objects = inProgram.objects.mapVals {
      case ObjectSignature(id, importedObjects, functions, directSupertypes, declPosOpt) =>
        ObjectSignature(id, importedObjects, functions.mapVals(typeFunSig), directSupertypes.map(typeNamedType), declPosOpt)
    }
    val datatypes = inProgram.datatypes.mapVals {
      case DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, declPosOpt) =>
        DatatypeSignature(id, typeParams.map(typeTypeTypeParam), directSupertypes.map(typeNamedType), directSubtypes, declPosOpt)
    }
    val records = inProgram.records.mapVals {
      case RecordSignature(id, typeParams, fields, directSupertypes, declPosOpt) =>
        RecordSignature(id, typeParams.map(typeTypeTypeParam), fields.mapVals(typeStableField), directSupertypes.map(typeNamedType), declPosOpt)
    }
    val outProgram = Program(inProgram.globalValuesContext,
      interfaces, classes, objects,
      datatypes, records,
      inProgram.typeAliases,
      inProgram.functions.mapVals(typeFunction)
    )
    (outProgram, ts)
  }

}
