package compiler.typechecking

import compiler.program.Program
import lang.{RuntimeTypeSignature, Variance}
import lang.Types.PrimitiveType.*
import lang.Types.{BaseType, NamedType, Type}

import scala.util.boundary

object BaseSubtypeRelation {

  extension (subT: Type) def baseSubtypeOf(superT: Type)(using program: Program): Boolean = {

    extension (subT: BaseType) infix def <<:(superT: BaseType): Boolean = (subT, superT) match {
      case _ if subT == superT => true
      case (NothingType, _) => true
      case (_, VoidType) => false
      case (VoidType, _) => false
      case (_, NothingType) => false
      case (NullType, _) => true
      case (_, NullType) => false
      case (_, AnyType) => true
      case (AnyType, _) => false
      case (NamedType(subtypeName, subtypeTypeArgs, subtypeArgs), NamedType(supertypeName, supertypeTypeArgs, supertypeArgs)) =>
        assert(subtypeArgs.isEmpty)
        assert(supertypeArgs.isEmpty)
        program.subToSuperSubst(subtypeName, supertypeName) match {
          case None => false
          case Some(declSubtypingSubst) =>
            val supertypeSig = program.resolveSignatureAs[RuntimeTypeSignature](supertypeName).get
            val subtypeSig = program.resolveSignatureAs[RuntimeTypeSignature](subtypeName).get
            val siteSubst = (subtypeSig.typeParams.map(_._1) zip subtypeTypeArgs).toMap
            val composedSubst = declSubtypingSubst.map {
              case (declSuperTypeTypeArgId, declSubTypeType: NamedType) if declSubTypeType.isSimpleName =>
                declSuperTypeTypeArgId -> siteSubst.getOrElse(declSubTypeType.typeName, declSubTypeType)
              case other => other
            }
            boundary {
              for (((typeParam, variance), typeInSuper) <- supertypeSig.typeParams zip supertypeTypeArgs) {
                val typeInSub = composedSubst.apply(typeParam)
                val typeArgsMatch = variance match {
                  case Variance.Invariant => typeInSub == typeInSuper
                  case Variance.Covariant => typeInSub.baseType <<: typeInSuper.baseType
                  case Variance.Contravariant => typeInSuper.baseType <<: typeInSub.baseType
                }
                if (!typeArgsMatch) {
                  boundary.break(false)
                }
              }
              true
            }
        }
      case _ => false
    }

    program.desugarType(subT).baseType <<: program.desugarType(superT).baseType
  }

}
