package compiler.typechecker

import lang.Capturables.*
import lang.CaptureDescriptors.*

import scala.collection.mutable

object SubcaptureRelation {

  extension (l: CaptureSet) def subcaptureOf(r: CaptureSet)(using ctx: TypeCheckingContext): Boolean = {
    SubcapturingComputer(ctx).isSubcapture(l, r)
  }

  extension (l: Capturable) def isCoveredBy(r: CaptureSet)(using ctx: TypeCheckingContext): Boolean = {
    SubcapturingComputer(ctx).isCovered(l, r)
  }

  /**
   * Defense mechanism against cyclic subcapturing on malformed programs
   */
  private class SubcapturingComputer(private val ctx: TypeCheckingContext) {
    private val stackedRequests = mutable.Set.empty[(Capturable, CaptureSet)]
    
    def isSubcapture(l: CaptureSet, r: CaptureSet): Boolean = {
      l.set.forall(isCovered(_, r))
    }

    def isCovered(l: Capturable, r: CaptureSet): Boolean = {
      val query = (l, r)
      if stackedRequests.contains(query) then false
      else {
        stackedRequests.add(query)
        val result = l match {
          case lCapt if r.set.contains(lCapt) => true
          case SelectPath(directRoot, field) if isCovered(directRoot, r) => true
          case lCapt: ConcreteCapturable if isSubcapture(ctx.lookup(lCapt).captureDescriptor, r) => true
          case _ => false
        }
        stackedRequests.remove(query)
        result
      }
    }

  }

}
