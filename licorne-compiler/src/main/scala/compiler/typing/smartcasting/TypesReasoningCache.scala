package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.{SealedInterfaceSignature, DataclassSignature}
import compiler.typing.contexts.ResolutionContext

import scala.collection.mutable
import scala.util.boundary


final class TypesReasoningCache(resolutionCtx: ResolutionContext) {
  private val allDataclasses = mutable.Map.empty[TypeIdentifier, Option[List[DataclassSignature]]]

  def developUnencapsulated(tpe: TypeIdentifier): Option[List[DataclassSignature]] = {
    allDataclasses.getOrElseUpdate(tpe, {
      val dataclassesOpt = boundary {
        resolutionCtx.resolveTypeSig(tpe) match {
          case Some(sig: SealedInterfaceSignature) =>
            val possibilities = mutable.ListBuffer.empty[DataclassSignature]
            for (subT <- sig.directSubtypes) {
              developUnencapsulated(subT) match {
                case Some(dataclasses) =>
                  possibilities.addAll(dataclasses)
                case None =>
                  boundary.break(None)
              }
            }
            Some(possibilities.toList.distinct)
          case Some(sig: DataclassSignature) => Some(List(sig))
          case _ => None
        }
      }
      allDataclasses(tpe) = dataclassesOpt
      dataclassesOpt
    })
  }

}
