package compiler.lang

import compiler.lang.Types.PrimitiveType.*
import compiler.lang.Types.{PrimitiveType, Type}
import compiler.stdlib.StdLib
import compiler.stdlib.StdLib.stringType

enum TypeConversion(val from: Type, val to: Type) {

  case Int2Double extends TypeConversion(IntType, DoubleType)
  case Double2Int extends TypeConversion(DoubleType, IntType)

  case IntToChar extends TypeConversion(IntType, StdLib.charType)
  case CharToInt extends TypeConversion(StdLib.charType, IntType)
}

object TypeConversion {

  def conversionFor(from: Type, to: Type): Option[TypeConversion] = {
    TypeConversion.values.find(conv => conv.from == from && conv.to == to)
  }

}
