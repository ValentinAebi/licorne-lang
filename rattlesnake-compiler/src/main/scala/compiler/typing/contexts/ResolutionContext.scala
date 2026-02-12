package compiler.typing.contexts

import compiler.identifiers.TypeIdentifier
import compiler.lang.*
import compiler.lang.Types.*
import compiler.typing.smartcasting.TypesReasoningCache
import compiler.util.zipCommons

import scala.reflect.ClassTag

final case class ResolutionContext(
                                    interfaces: Map[TypeIdentifier, InterfaceSignature],
                                    classes: Map[TypeIdentifier, ClassSignature],
                                    objects: Map[TypeIdentifier, ObjectSignature],
                                    datatypes: Map[TypeIdentifier, DatatypeSignature],
                                    records: Map[TypeIdentifier, RecordSignature]
                                  ) {
  
  val typesReasoningCache: TypesReasoningCache = TypesReasoningCache(this)

  def resolveSignature(typeId: TypeIdentifier): Option[TypeSignature] =
    (interfaces.get(typeId)
      orElse classes.get(typeId)
      orElse objects.get(typeId)
      orElse datatypes.get(typeId)
      orElse records.get(typeId))

  def resolveSignatureAs[S <: TypeSignature : ClassTag](typeId: TypeIdentifier): Option[S] =
    resolveSignature(typeId) match {
      case Some(sig: S) => Some(sig)
      case _ => None
    }

}
