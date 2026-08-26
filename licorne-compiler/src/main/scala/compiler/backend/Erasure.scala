package compiler.backend

import compiler.lang.Types.PrimitiveType.{AnyType, IntType}
import compiler.lang.Types.*
import compiler.stdlib.StdLib
import compiler.typing.contexts.DealiasingContext

object Erasure {

  def getRuntimeType(tpe: Type)(using dealiasingCtx: DealiasingContext): Type = dealiasingCtx.dealiasType(tpe) match {
    case NamedType(StdLib.arrayTypeId, List(elemType), Nil) =>
      NamedType(StdLib.arrayTypeId, List(getRuntimeType(elemType.withTypeVarsExpanded)), List.empty)
    case NamedType(tid, tArgs, args) => NamedType(tid, tArgs.map(getRuntimeType), List.empty)
    case tv: TypeVariable => getRuntimeType(tv.upperBoundOpt.getOrElse(NullableType(AnyType)))
    case _: IntRangeType => IntType
    case RefinedType(baseType, predicate) => getRuntimeType(baseType)
    case NullableType(nullatedType) => NullableType(getRuntimeType(nullatedType))
    case UnionType(types) => UnionType(types.map(getRuntimeType))
    case IntersectionType(types) => IntersectionType(types.map(getRuntimeType))
    case ClosureType(params, result, enforcedPure) => ???
    case tpe: PrimitiveType => tpe
  }

}
