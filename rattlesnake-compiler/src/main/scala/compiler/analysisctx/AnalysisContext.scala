package compiler.analysisctx

import compiler.pipeline.CompilationStep.ContextCreation
import compiler.reporting.Errors.{Err, ErrorReporter}
import compiler.reporting.Position
import compiler.valuesconversion.GlobalValuesContext
import identifiers.TypeIdentifier
import lang.*

import scala.collection.mutable

final case class AnalysisContext(
                                  globalValuesContext: GlobalValuesContext,
                                  classes: Map[TypeIdentifier, ClassSignature],
                                  packages: Map[TypeIdentifier, ObjectSignature],
                                  structs: Map[TypeIdentifier, StructSignature],
                                  typeAliases: Map[TypeIdentifier, TypeAliasSignature]
                                )

object AnalysisContext {

  private[analysisctx] final class Builder(er: ErrorReporter) {
    private val signatures = mutable.Map.empty[TypeIdentifier, TypeSignature]

    val globalValuesContext: GlobalValuesContext = GlobalValuesContext()

    def saveSignature(sig: TypeSignature, posOpt: Option[Position]): Unit = {
      if (signatures.contains(sig.id)) {
        er.push(Err(ContextCreation, s"redefinition of type ${sig.id}", posOpt))
      } else {
        signatures(sig.id) = sig
      }
    }

    def build(): AnalysisContext = {
      val classesB = Map.newBuilder[TypeIdentifier, ClassSignature]
      val packagesB = Map.newBuilder[TypeIdentifier, ObjectSignature]
      val structsB = Map.newBuilder[TypeIdentifier, StructSignature]
      val typeAliasesB = Map.newBuilder[TypeIdentifier, TypeAliasSignature]
      for ((id, sig) <- signatures) {
        sig match {
          case sig: ClassSignature => classesB.addOne((id, sig))
          case sig: ObjectSignature => packagesB.addOne((id, sig))
          case sig: StructSignature => structsB.addOne((id, sig))
          case sig: TypeAliasSignature => typeAliasesB.addOne((id, sig))
        }
      }
      AnalysisContext(
        globalValuesContext,
        classesB.result(),
        packagesB.result(),
        structsB.result(),
        typeAliasesB.result()
      )
    }
  }

}
