package compiler.reasoning

import compiler.lang.Types.PrimitiveType.{BoolType, IntType}
import compiler.lang.Types.{IntRangeType, Type, asRefinedType}
import compiler.typing.contexts.DealiasingContext
import compiler.valuesconversion.GlobalValuesContext
import io.ksmt.sort.{KBoolSort, KSort, KUninterpretedSort}

enum SimplifiedType[S <: KSort] {
  case Integer[IntSort <: KSort]() extends SimplifiedType[IntSort]
  case Boolean extends SimplifiedType[KBoolSort]
  case Object extends SimplifiedType[KUninterpretedSort]
}

object SimplifiedType {

  def from[IntSort <: KSort](tpe: Type)(using dealiasingCtx: DealiasingContext, globalValsCtx: GlobalValuesContext): SimplifiedType[?] =
    dealiasingCtx.dealiasType(tpe).withTypeVarsExpanded.asRefinedType.baseType match {
      case IntType => SimplifiedType.Integer[IntSort]()
      case _: IntRangeType => SimplifiedType.Integer[IntSort]()
      case BoolType => SimplifiedType.Boolean
      case _ => SimplifiedType.Object
    }

}
