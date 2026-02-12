package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.{DatatypeSignature, RecordSignature}
import compiler.typing.contexts.ResolutionContext

import scala.collection.mutable
import scala.util.boundary


final class TypesReasoningCache(resolutionCtx: ResolutionContext) {
  private val allRecords = mutable.Map.empty[TypeIdentifier, Option[List[RecordSignature]]]

  def developUnencapsulated(tpe: TypeIdentifier): Option[List[RecordSignature]] = {
    allRecords.getOrElseUpdate(tpe, {
      val recordsOpt = boundary {
        resolutionCtx.resolveSignature(tpe) match {
          case Some(sig: DatatypeSignature) =>
            val possibilities = mutable.ListBuffer.empty[RecordSignature]
            for (subT <- sig.directSubtypes) {
              developUnencapsulated(subT) match {
                case Some(records) =>
                  possibilities.addAll(records)
                case None =>
                  boundary.break(None)
              }
            }
            Some(possibilities.toList.distinct)
          case Some(sig: RecordSignature) => Some(List(sig))
          case _ => None
        }
      }
      allRecords(tpe) = recordsOpt
      recordsOpt
    })
  }

}
