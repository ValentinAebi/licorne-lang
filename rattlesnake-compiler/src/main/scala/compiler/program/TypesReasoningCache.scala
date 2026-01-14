package compiler.program

import identifiers.TypeIdentifier
import lang.{DatatypeSignature, RecordSignature}

import scala.collection.mutable


final class TypesReasoningCache(program: Program) {
  private val allRecords = mutable.Map.empty[TypeIdentifier, Option[List[RecordSignature]]]

  def developUnencapsulated(tpe: TypeIdentifier): Option[List[RecordSignature]] = {

    def develop(tid: TypeIdentifier): Option[List[RecordSignature]] = {
      program.resolveSignature(tid) match {
        case Some(sig: DatatypeSignature) =>
          sig.directSubtypes.toList.foldLeft(Option(List.empty[RecordSignature])) { (lsOpt, stid) =>
            for {
              ls <- lsOpt
              newElems <- develop(stid)
            } yield (ls ++ newElems).distinct
          }
        case Some(sig: RecordSignature) =>
          Some(List(sig))
        case _ =>
          None
      }
    }

    allRecords.getOrElseUpdate(tpe, {
      val recordsOpt = develop(tpe)
      allRecords(tpe) = recordsOpt
      recordsOpt
    })
  }

}
