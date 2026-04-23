package compiler.smt

import compiler.lang.Types
import compiler.lang.Types.PrimitiveType.{BoolType, IntType}
import compiler.lang.Types.{IntRangeType, Type}
import compiler.typing.contexts.DealiasingContext
import io.ksmt.sort.{KBoolSort, KIntSort, KSort, KUninterpretedSort}

enum SimplifiedType[S <: KSort] {
  case Integer extends SimplifiedType[KIntSort]
  case Boolean extends SimplifiedType[KBoolSort]
  case Object extends SimplifiedType[KUninterpretedSort]
}

object SimplifiedType {
  
  def from(tpe: Type)(using dealiasingCtx: DealiasingContext): SimplifiedType[?] = dealiasingCtx.dealiasType(tpe) match {
    case IntType => SimplifiedType.Integer
    case _: IntRangeType => SimplifiedType.Integer
    case BoolType => SimplifiedType.Boolean
    case _ => SimplifiedType.Object
  }
  
}
