package compiler.typechecking

import compiler.program.Program
import identifiers.TypeIdentifier
import lang.Types.{NamedType, Type}

import scala.util.boundary

object TypeInference {

  def unifyInfer(typeModel: Type, typeParamsInModel: Set[TypeIdentifier], actualType: Type)(using program: Program): Option[Map[TypeIdentifier, Type]] = (program.desugarType(typeModel), program.desugarType(actualType)) match {
    case (typeModel, actualType) if typeModel == actualType => Some(Map.empty)
    case (typeModel@NamedType(typeModelName, Nil, Nil), actualType) if typeParamsInModel.contains(typeModelName) =>
      Some(Map(typeModelName -> actualType))
    case (typeModel@NamedType(typeModelName, typeModelTypeArgs, typeModelArgs), actualType@NamedType(actualTypeName, actualTypeTypeArgs, actualTypeArgs)) if typeModelTypeArgs.size == actualTypeTypeArgs.size =>
      assert(typeModelArgs.isEmpty)
      assert(actualTypeArgs.isEmpty)
      program.subToSuperSubst(actualTypeName, typeModelName) match {
        case None => None
        case Some(localSubst) =>
          boundary {
            val transSubst = (typeModelTypeArgs zip actualTypeTypeArgs).foldLeft(Seq.empty[(TypeIdentifier, Type)]) {
              case (prevSubst, (typeModelTypeArg, actualTypeTypeArg)) =>
                unifyInfer(typeModelTypeArg, typeParamsInModel, actualTypeTypeArg) match {
                  case Some(currSubst) => prevSubst ++ currSubst
                  case None =>
                    boundary.break(None)
                }
            }
            val groups = transSubst.groupBy((tid, _) => tid).map((tid, group) => (tid, group.map((tid, tpe) => tpe).toSet))
            groups.find((tid, group) => group.size != 1).foreach {
              boundary.break(None)
            }
            Some {
              groups.map((tid, group) => tid -> (group.head match {
                case tpe@NamedType(name, Nil, Nil) => localSubst.getOrElse(name, tpe)
                case tpe => tpe
              }))
            }
          }
      }
    case _ => None
  }

}
