package compiler.typechecking

import compiler.program.Program
import identifiers.TypeIdentifier
import lang.Types.{BaseType, NamedType, RefinedType, Type}
import lang.Variance
import lang.Types.PrimitiveType.*

import scala.collection.mutable

object SubtypeRelation {
  
  extension (subT: Type) def shapeSubtype(superT: Type)(using tcCtx: TypeCheckingContext): Boolean = {
    
    val isShapeSubtypeOf: Unit = ()
    
    extension (subT: BaseType) infix def <<:(superT: BaseType): Boolean = (subT, superT) match {
      case (NothingType, _) => true
      case (_, VoidType) => false
      case (VoidType, _) => false
      case _ if subT == superT => true
      case (_, NothingType) => false
      case (NullType, _) => true
      case (_, NullType) => false
//      case (NamedType(subName, subTypeArgs, subArgs, subIsPure), NamedType(superName, superTypeArgs, superArgs, superIsPure)) =>
//        if superIsPure && !subIsPure then false
//        else if 
    }
    
    tcCtx.desugarType(subT).baseType <<: tcCtx.desugarType(superT).baseType
  }
  
  
  
}
