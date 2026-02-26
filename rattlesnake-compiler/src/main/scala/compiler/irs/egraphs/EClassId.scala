package compiler.irs.egraphs

import java.util.concurrent.atomic.AtomicLong

case class EClassId private(private val uid: Long) extends AnyVal

object EClassId {
  
  final class Generator {
    private val counter = AtomicLong(0)
    
    def next(): EClassId =
      EClassId(counter.incrementAndGet())
    
  }
  
}
