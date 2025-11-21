package compiler.analysisctx

import compiler.datastructures.Graph
import compiler.pipeline.CompilationStep.SSAGeneration
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.GlobalValuesContext
import identifiers.TypeIdentifier
import lang.*
import lang.Types.Type

import scala.collection.mutable

final case class AnalysisContext(
                                  globalValuesContext: GlobalValuesContext,
                                  interfaces: Map[TypeIdentifier, InterfaceSignature],
                                  classes: Map[TypeIdentifier, ClassSignature],
                                  objects: Map[TypeIdentifier, ObjectSignature],
                                  datatypes: Map[TypeIdentifier, DatatypeSignature],
                                  structs: Map[TypeIdentifier, StructSignature],
                                  typeAliases: Map[TypeIdentifier, TypeAliasSignature]
                                ) {
  
  def performCyclicityChecks(er: ErrorReporter): Unit = {
    checkSubtypingCyclicity(er)
    checkObjectImportsCyclicity(er)
    checkTypeAliasCyclicity(er)
    // TODO also check that names refer to known types
  }
  
  private def checkSubtypingCyclicity(er: ErrorReporter): Unit = {
    ??? // TODO using Graph
  }
  
  private def checkObjectImportsCyclicity(er: ErrorReporter): Unit = {
    ??? // TODO using Graph
  }
  
  private def checkTypeAliasCyclicity(er: ErrorReporter): Unit = {
    ??? // TODO using Graph
  }
  
}

object AnalysisContext {

  final class Builder(er: ErrorReporter) {
    private val signatures = mutable.Map.empty[TypeIdentifier, TypeSignature]

    val globalValuesContext: GlobalValuesContext = GlobalValuesContext()

    def saveSignature(sig: TypeSignature, posOpt: Option[Position]): Unit = {
      if (signatures.contains(sig.id)) {
        er.push(Err(SSAGeneration, s"redefinition of type ${sig.id}", posOpt))
      } else {
        signatures(sig.id) = sig
      }
    }

    def build(): AnalysisContext = {
      val interfacesB = Map.newBuilder[TypeIdentifier, InterfaceSignature]
      val classesB = Map.newBuilder[TypeIdentifier, ClassSignature]
      val packagesB = Map.newBuilder[TypeIdentifier, ObjectSignature]
      val datatypes = Map.newBuilder[TypeIdentifier, DatatypeSignature]
      val structsB = Map.newBuilder[TypeIdentifier, StructSignature]
      val typeAliasesB = Map.newBuilder[TypeIdentifier, TypeAliasSignature]
      for ((id, sig) <- signatures) {
        sig match {
          case sig: InterfaceSignature => interfacesB.addOne(id, sig)
          case sig: ClassSignature => classesB.addOne(id, sig)
          case sig: ObjectSignature => packagesB.addOne(id, sig)
          case sig: DatatypeSignature => datatypes.addOne(id, sig)
          case sig: StructSignature => structsB.addOne(id, sig)
          case sig: TypeAliasSignature => typeAliasesB.addOne(id, sig)
        }
      }
      AnalysisContext(
        globalValuesContext,
        interfacesB.result(),
        classesB.result(),
        packagesB.result(),
        datatypes.result(),
        structsB.result(),
        typeAliasesB.result()
      )
    }
  }

}
