package compiler.backend

import compiler.irs.ssa.Formulas.IdValue
import compiler.lang.FunctionSignature
import compiler.lang.Types.Type
import compiler.reporting.Position
import compiler.typing.contexts.TypeParamsContext
import compiler.valuesconversion.GlobalValuesContext

import java.lang.classfile.TypeKind
import scala.collection.mutable


// TODO slots assignment could be optimized (using register allocation techniques...)
final class FunctionGenerationContext(globalValsCtx: GlobalValuesContext, val typeParamsCtx: TypeParamsContext, val enclosingFunc: FunctionSignature) {
  private val slotsAssignment = mutable.Map.empty[IdValue, Int]
  private var nextFreeSlot = 0
  private var currLineNumber = 0

  def isNullVal(idVal: IdValue): Boolean =
    idVal == globalValsCtx.nullVal
  
  def onNewLineNumber(posOpt: Option[Position])(action: Int => Unit): Unit = posOpt match {
    case Some(Position(srcCodeProviderName, line, col)) if line != currLineNumber =>
      currLineNumber = line
      action(line)
    case _ => ()
  }

  def getSlot(idVal: IdValue): Int =
    slotsAssignment.apply(idVal)

  def getOrAllocSlot(kind: TypeKind, idVal: IdValue): Int = {
    if (hasSlotFor(idVal)) {
      getSlot(idVal)
    } else {
      allocateSlot(kind, idVal)
    }
  }

  def hasSlotFor(idVal: IdValue): Boolean =
    slotsAssignment.contains(idVal)

  def allocateSlot(kind: TypeKind, idVal: IdValue): Int =
    allocateSlot(kind.slotSize(), idVal)

  def allocateSlot(slotSize: Int, idVal: IdValue): Int = {
    require(!hasSlotFor(idVal))
    val slot = allocateSlotOfSize(slotSize)
    slotsAssignment(idVal) = slot
    slot
  }

  def coalesce(alrKnownVal: IdValue, newVal: IdValue): Unit = {
    require(hasSlotFor(alrKnownVal))
    require(!hasSlotFor(newVal))
    slotsAssignment(newVal) = getSlot(alrKnownVal)
  }

  private def allocateSlotOfSize(size: Int): Int = {
    val slot = nextFreeSlot
    nextFreeSlot += size
    slot
  }

}
