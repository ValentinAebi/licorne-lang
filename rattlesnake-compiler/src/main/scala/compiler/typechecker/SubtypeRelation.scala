package compiler.typechecker

import compiler.typechecker.SubcaptureRelation.subcaptureOf
import compiler.typechecker.TypeCheckingContext
import identifiers.TypeIdentifier
import lang.Types.*
import lang.Types.PrimitiveTypeShape.*
import lang.StructSignature

import scala.collection.mutable

object SubtypeRelation {

  extension (l: Type) def subtypeOf(r: Type)(using tcCtx: TypeCheckingContext): Boolean = {
    l.shape.subtypeOf(r.shape) && l.captureDescriptor.subcaptureOf(r.captureDescriptor)
  }

  extension (subT: TypeShape) def subtypeOf(superT: TypeShape)(using TypeCheckingContext): Boolean = {
    (subT, superT) match {
      case _ if subT == superT => true
      case (NothingType | UndefinedTypeShape, _) => true
      case (NamedTypeShape(subId), NamedTypeShape(superId)) =>
        substructOf(subId, superId)
      case (ArrayTypeShape(subElemType), ArrayTypeShape(superElemType)) =>
        subElemType == superElemType
      case (UnionTypeShape(subTypes), superT) =>
        subTypes.forall(_.subtypeOf(superT))
      case (subT, UnionTypeShape(superTypes)) =>
        superTypes.exists(subT.subtypeOf(_))
      case _ => false
    }
  }

  def substructOf(subT: TypeIdentifier, superT: TypeIdentifier)(using tcCtx: TypeCheckingContext): Boolean = {
    // BFS

    val worklist = mutable.Queue.empty[TypeIdentifier]
    val alreadyAdded = mutable.Set.empty[TypeIdentifier]

    def registerIfNew(tid: TypeIdentifier): Unit = {
      if (!alreadyAdded.contains(tid)) {
        worklist.enqueue(tid)
        alreadyAdded.addOne(tid)
      }
    }

    registerIfNew(subT)
    while (worklist.nonEmpty) {
      val curr = worklist.dequeue()
      if (curr == superT) {
        return true
      }
      tcCtx.structs.get(curr).foreach(_.directSupertypes.foreach(registerIfNew))
    }
    false
  }

  private def logicalImplies(a: Boolean, b: Boolean): Boolean = (!a || b)

}
