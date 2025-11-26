package compiler.typechecking

import lang.RuntimeTypeSignature
import lang.Types.PrimitiveType.*
import lang.Types.{BaseType, NamedType, Type}

object BaseSubtypeRelation {

  extension (subT: Type) def baseSubtypeOf(superT: Type)(using tcCtx: TypeCheckingContext): Boolean = {

    extension (subT: BaseType) infix def <<:(superT: BaseType): Boolean = (subT, superT) match {
      case (NothingType, _) => true
      case (_, VoidType) => false
      case (VoidType, _) => false
      case _ if subT == superT => true
      case (_, NothingType) => false
      case (NullType, _) => true
      case (_, NullType) => false
      case (NamedType(subtypeName, subtypeTypeArgs, subtypeArgs), NamedType(supertypeName, _, supertypeArgs)) =>
        assert(subtypeArgs.isEmpty)
        assert(supertypeArgs.isEmpty)
        tcCtx.program.subToSuperSubst(subtypeName, supertypeName) match {
          case None => false
          case Some(declSubtypingSubst) =>
            val subtypeSig = tcCtx.program.resolveSignatureAs[RuntimeTypeSignature](subtypeName).get
            val siteSubst = (subtypeSig.typeParams.map(_._1) zip subtypeTypeArgs).toMap
            subtypeSig.toType(siteSubst, Map.empty) == superT
        }
      case _ => false
    }

    tcCtx.desugarType(subT).baseType <<: tcCtx.desugarType(superT).baseType
  }

}
