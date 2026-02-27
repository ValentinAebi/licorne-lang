package compiler.typing.smartcasting

import compiler.identifiers.TypeIdentifier
import compiler.lang.Formulas.{Formula, IdValue}
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{DatatypeSignature, Encapsulated, Formulas, RecordSignature, Unencapsulated}
import compiler.program.Program
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult
import compiler.typing.contexts.SubtypingContext.DowncastTargetCheckResult.*
import compiler.typing.contexts.{ResolutionContext, SubtypingContext}
import compiler.lang.Formulas.*

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.boundary

trait ControlFlowInfo {

  def smartcastFor(formula: Formula): Option[Type]

  def hasExited: Boolean
}

final class EnabledControlFlowInfo extends ControlFlowInfo {

  def smartcastFor(formula: Formula): Option[Type] = ???

  def hasExited: Boolean = ???

}

object DisabledControlFlowInfo extends ControlFlowInfo {
  override def smartcastFor(formula: Formula): Option[Type] = None

  override def hasExited: Boolean = false
}

object ControlFlowInfo {

  def emptyEnabled(subtypingCtx: SubtypingContext): EnabledControlFlowInfo = ???

  def disabled: DisabledControlFlowInfo.type = DisabledControlFlowInfo

}
