package compiler.typing.contexts

import compiler.identifiers.TypeIdentifier
import compiler.lang.TypeParamInfo

import scala.reflect.ClassTag

final case class TypeParamsContext(typeParams: Map[TypeIdentifier, TypeParamInfo]) {

  def resolve(tid: TypeIdentifier): Option[TypeParamInfo] = typeParams.get(tid)

  def resolveAs[T <: TypeParamInfo : ClassTag](tid: TypeIdentifier): Option[T] = {
    resolve(tid) match {
      case Some(tpInfo: T) => Some(tpInfo)
      case _ => None
    }
  }

  def extendedWith(newTypeParam: TypeParamInfo): TypeParamsContext =
    TypeParamsContext(typeParams + (newTypeParam.tid -> newTypeParam))

  def extendedWith(newTypeParams: Iterable[TypeParamInfo]): TypeParamsContext =
    TypeParamsContext(typeParams ++ newTypeParams.map(tp => tp.tid -> tp))

}

object TypeParamsContext {

  def apply(typeParams: Iterable[TypeParamInfo]): TypeParamsContext =
    TypeParamsContext(typeParams.map(tParam => tParam.tid -> tParam).toMap)

  def empty: TypeParamsContext = TypeParamsContext(Map.empty)

  def processTypeParamsAccumulating[T <: TypeParamInfo, U](initialTypeParamsCtx: TypeParamsContext, typeParamsRaw: Iterable[U])
                                                          (action: U => TypeParamsContext ?=> T): (List[T], TypeParamsContext) = {
    val typeParamsInstB = List.newBuilder[T]
    var typeParamsCtx = initialTypeParamsCtx
    for (tParamRaw <- typeParamsRaw) {
      val tParamInst = action(tParamRaw)(using typeParamsCtx)
      typeParamsInstB.addOne(tParamInst)
      typeParamsCtx = typeParamsCtx.extendedWith(tParamInst)
    }
    (typeParamsInstB.result(), typeParamsCtx)
  }

}
