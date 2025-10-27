package compiler.analysisctx

import identifiers.TypeIdentifier
import lang.{ClassSignature, PackageSignature, StructSignature, TypeAliasSignature}

import scala.collection.mutable

final case class AnalysisContext(
                                classes: Map[TypeIdentifier, ClassSignature],
                                packages: Map[TypeIdentifier, PackageSignature],
                                structs: Map[TypeIdentifier, StructSignature],
                                typeAliases: Map[TypeIdentifier, TypeAliasSignature]
                                )

object AnalysisContext {

  private[analysisctx] final class Builder {
    private val classes = mutable.Map.empty[TypeIdentifier, ClassSignature]
    private val packages = mutable.Map.empty[TypeIdentifier, PackageSignature]
    private val structs = mutable.Map.empty[TypeIdentifier, StructSignature]
    private val typeAliases = mutable.Map.empty[TypeIdentifier, TypeAliasSignature]
    
    

  }

}
