package compiler.egraphs

import java.util.concurrent.atomic.AtomicLong

case class EClassId private(private val uid: Long) extends Comparable[EClassId] {
  override def compareTo(that: EClassId): Int = this.uid.compareTo(that.uid)

  override def toString: String = s"cl$uid"
}

object EClassId {
  
  final class Generator {
    private val counter = AtomicLong(-1)
    
    def next(): EClassId =
      EClassId(counter.incrementAndGet())
    
  }
  
}
