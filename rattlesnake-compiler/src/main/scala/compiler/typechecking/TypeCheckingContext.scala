package compiler.typechecking

import compiler.program.Program
import compiler.typechecking.TypeCheckingContext.TypeInfo
import identifiers.TypeIdentifier
import lang.Types.{BaseType, Type}
import lang.{DatatypeSignature, StructSignature, UnencapsulatedTypeSignature}
import lang.Values.IdValue

import scala.annotation.tailrec
import scala.util.boundary

final case class TypeCheckingContext(
                                      program: Program,
                                      typeInfos: Map[IdValue, TypeInfo],
                                      thisVal: IdValue,
                                      alwaysExitsFlag: Boolean
                                    ) {

  def withTypeInfoRefined(newTypeInfos: Set[TypeInfo]): TypeCheckingContext =
    copy(typeInfos = newTypeInfos.groupBy(_.value).map { (idValue, allInfos) =>
      val knownIs = allInfos.flatMap(_.knownIs)
      val knownIsNot = allInfos.flatMap(_.knownIsNot)
      idValue -> TypeInfo(idValue, allInfos.head.tpe, knownIs, knownIsNot)
    })

  def withAlwaysExitsFlagRaised: TypeCheckingContext = copy(alwaysExitsFlag = true)
  
  def inferredTypeFor(idValue: IdValue): Option[TypeIdentifier] =
    typeInfos.get(idValue).flatMap(_.mostPreciseType(using program))

}

object TypeCheckingContext {

  final case class TypeInfo(value: IdValue, tpe: TypeIdentifier, knownIs: Set[TypeIdentifier], knownIsNot: Set[TypeIdentifier]) {

    def mergedWith(that: TypeInfo): TypeInfo = {
      require(this.value == that.value)
      require(this.tpe == that.tpe)
      TypeInfo(value, tpe, this.knownIs ++ that.knownIs, this.knownIsNot ++ that.knownIsNot)
    }

    /**
     * @return None if all possible types where excluded (in the typical context this implies that we are in an unreachable branch)
     */
    def mostPreciseType(using program: Program): Option[TypeIdentifier] = boundary {

      @tailrec def narrowDown(front: Set[TypeIdentifier]): Set[TypeIdentifier] = {
        val narrowed = (front -- knownIsNot).flatMap {
          program.resolveSignature(_) match {
            case Some(datatypeSignature: DatatypeSignature) => datatypeSignature.directSubtypes
            case Some(structSignature: StructSignature) => Set(structSignature.id)
            case _ => Set.empty
          }
        }
        if narrowed == front then front else narrowDown(narrowed)
      }
      
      val front = narrowDown(Set(tpe))
      front.size match {
        case 0 => None
        case 1 => Some(front.head)
        case _ => Some(tpe)
      }
    }

  }

}
