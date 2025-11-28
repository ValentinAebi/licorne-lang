package compiler.typechecking

import compiler.program.Program
import lang.RuntimeTypeSignature
import lang.Types.PrimitiveType.*
import lang.Types.{BaseType, NamedType, Type}

object BaseSubtypeRelation {

  extension (subT: Type) def baseSubtypeOf(superT: Type)(using program: Program): Boolean = {

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
        program.subToSuperSubst(subtypeName, supertypeName) match {
          case None => false
          case Some(declSubtypingSubst) =>
            val supertypeSig = program.resolveSignatureAs[RuntimeTypeSignature](supertypeName).get
            val subtypeSig = program.resolveSignatureAs[RuntimeTypeSignature](subtypeName).get
            val siteSubst = (subtypeSig.typeParams.map(_._1) zip subtypeTypeArgs).toMap
            supertypeSig.toType(siteSubst, Map.empty) == superT
        }
      case _ => false
    }

    program.desugarType(subT).baseType <<: program.desugarType(superT).baseType
  }

}
