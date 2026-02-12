package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{Formula, IdValue}
import compiler.lang.Types.NamedType
import compiler.lang.{DatatypeSignature, Encapsulated, RecordSignature, Unencapsulated}
import compiler.program.Program
import compiler.typing.contexts.ResolutionContext

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary

final class ControlFlowInfo {
  private val unencapsulatedTypesData = mutable.Map.empty[Formula, UnencapsulatedSmartcastingData]
  private val encapsulatedTypesData = mutable.Map.empty[Formula, EncapsulatedSmartcastingData]
  
  
  
}

object ControlFlowInfo {

  val empty: ControlFlowInfo = new ControlFlowInfo

}
