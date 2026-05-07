package compiler.smt

import compiler.lang.Types.PrimitiveType.{BoolType, IntType}
import compiler.lang.Types.{IntRangeType, Type}
import compiler.typing.contexts.DealiasingContext
import io.ksmt.sort.{KBoolSort, KSort, KUninterpretedSort}

enum SimplifiedType[S <: KSort] {
  case Integer[IntSort <: KSort]() extends SimplifiedType[IntSort]
  case Boolean extends SimplifiedType[KBoolSort]
  case Object extends SimplifiedType[KUninterpretedSort]
}

object SimplifiedType {
  
  def from[IntSort <: KSort](tpe: Type)(using dealiasingCtx: DealiasingContext): SimplifiedType[?] = dealiasingCtx.dealiasType(tpe) match {
    case IntType => SimplifiedType.Integer[IntSort]()
    case _: IntRangeType => SimplifiedType.Integer[IntSort]()
    case BoolType => SimplifiedType.Boolean
    case _ => SimplifiedType.Object
  }
  
}
