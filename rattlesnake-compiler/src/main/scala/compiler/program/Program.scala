package compiler.program

import compiler.identifiers.TypeIdentifier
import compiler.irs.SSA
import compiler.lang.*
import compiler.lang.Types.PrimitiveType
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.GlobalValuesContext

import scala.collection.immutable.SeqMap
import scala.collection.mutable

final case class Program(
                          globalValuesContext: GlobalValuesContext,
                          interfaces: SeqMap[TypeIdentifier, InterfaceSignature],
                          classes: SeqMap[TypeIdentifier, ClassSignature],
                          objects: SeqMap[TypeIdentifier, ObjectSignature],
                          datatypes: SeqMap[TypeIdentifier, DatatypeSignature],
                          records: SeqMap[TypeIdentifier, RecordSignature],
                          typeAliases: SeqMap[TypeIdentifier, TypeAliasSignature],
                          functions: SeqMap[FunctionSignature, SSA.Function],
                          loops: Seq[SSA.Loop]
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

    def build(allFunctions: SeqMap[FunctionSignature, SSA.Function], loops: Seq[SSA.Loop]): Program = {
      val interfacesB = SeqMap.newBuilder[TypeIdentifier, InterfaceSignature]
      val classesB = SeqMap.newBuilder[TypeIdentifier, ClassSignature]
      val packagesB = SeqMap.newBuilder[TypeIdentifier, ObjectSignature]
      val datatypes = SeqMap.newBuilder[TypeIdentifier, DatatypeSignature]
      val recordsB = SeqMap.newBuilder[TypeIdentifier, RecordSignature]
      val typeAliasesB = SeqMap.newBuilder[TypeIdentifier, TypeAliasSignature]
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
        allFunctions,
        loops
      )
    }
  }

}
