package compiler.backend

import java.lang.constant.ClassDesc
import java.lang.constant.ConstantDescs.{CD_Boolean, CD_Character, CD_Double, CD_Integer, CD_boolean, CD_char, CD_double, CD_int}

object Boxing {

  def boxDesc(cd: ClassDesc): ClassDesc = cd match {
    case CD_boolean => CD_Boolean
    case CD_int => CD_Integer
    case CD_char => CD_Character
    case CD_double => CD_Double
    case cd => cd
  }
  
  def unboxDesc(cd: ClassDesc): ClassDesc = cd match {
    case CD_Boolean => CD_boolean
    case CD_Integer => CD_int
    case CD_Character => CD_char
    case CD_Double => CD_double
    case cd => cd
  }
  
}
