package compiler.program

import compiler.datastructures.Graph
import compiler.identifiers.{ThisId, TypeIdentifier}
import compiler.irs.ssa.SSA
import compiler.lang.Formulas.{And, Formula, IdValue}
import compiler.lang.Types.PrimitiveType.UnitType
import compiler.lang.Types.{PrimitiveType, Type, TypeVariable}
import compiler.lang.Visibility.Private
import compiler.lang.*
import compiler.lang.Variance.Contravariant
import compiler.pipeline.CompilationStep
import compiler.pipeline.CompilationStep.{SSAGeneration, TypeChecking}
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.typing.phases.TyperPhase1
import compiler.typing.smartcasting.TypesReasoningCache
import compiler.util.zipCommons
import compiler.valuesconversion.GlobalValuesContext

import java.util
import scala.collection.{SeqMap, mutable}
import scala.reflect.ClassTag
import scala.util.boundary

final case class Program(
                          globalValuesContext: GlobalValuesContext,
                          interfaces: Map[TypeIdentifier, InterfaceSignature],
                          classes: Map[TypeIdentifier, ClassSignature],
                          objects: Map[TypeIdentifier, ObjectSignature],
                          datatypes: Map[TypeIdentifier, DatatypeSignature],
                          records: Map[TypeIdentifier, RecordSignature],
                          typeAliases: Map[TypeIdentifier, TypeAliasSignature],
                          functions: SeqMap[FunctionSignature, SSA.Function]
                        ) {

  def runtimeSignatures: Iterable[RuntimeTypeSignature] = (interfaces ++ classes ++ objects ++ datatypes ++ records).values

  def allTypeSignatures: Iterable[TypeSignature] = runtimeSignatures ++ typeAliases.values

}

object Program {

  final class Builder(er: ErrorReporter) {
    private val signatures = mutable.LinkedHashMap.empty[TypeIdentifier, TypeSignature]

    val globalValuesContext: GlobalValuesContext = GlobalValuesContext()

    def saveSignature(sig: TypeSignature, posOpt: Option[Position]): Unit = {
      if (PrimitiveType.values.exists(_.str == sig.id.toString)) {
        er.report(Err(SSAGeneration, s"identifier ${sig.id} is illegal since it conflicts with a primitive type", posOpt))
      } else if (signatures.contains(sig.id)) {
        er.report(Err(SSAGeneration, s"redefinition of type ${sig.id}", posOpt))
      } else {
        signatures(sig.id) = sig
      }
    }

    def build(allFunctions: SeqMap[FunctionSignature, SSA.Function]): Program = {
      val interfacesB = Map.newBuilder[TypeIdentifier, InterfaceSignature]
      val classesB = Map.newBuilder[TypeIdentifier, ClassSignature]
      val packagesB = Map.newBuilder[TypeIdentifier, ObjectSignature]
      val datatypes = Map.newBuilder[TypeIdentifier, DatatypeSignature]
      val recordsB = Map.newBuilder[TypeIdentifier, RecordSignature]
      val typeAliasesB = Map.newBuilder[TypeIdentifier, TypeAliasSignature]
      for ((id, sig) <- signatures) {
        sig match {
          case sig: InterfaceSignature => interfacesB.addOne(id, sig)
          case sig: ClassSignature => classesB.addOne(id, sig)
          case sig: ObjectSignature => packagesB.addOne(id, sig)
          case sig: DatatypeSignature => datatypes.addOne(id, sig)
          case sig: RecordSignature => recordsB.addOne(id, sig)
          case sig: TypeAliasSignature => typeAliasesB.addOne(id, sig)
        }
      }
      Program(
        globalValuesContext,
        interfacesB.result(),
        classesB.result(),
        packagesB.result(),
        datatypes.result(),
        recordsB.result(),
        typeAliasesB.result(),
        allFunctions
      )
    }
  }

}
