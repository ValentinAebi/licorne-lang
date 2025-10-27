package lang

import identifiers.{FunOrVarId, NormalTypeId, TypeIdentifier}
import lang.CaptureDescriptors.CaptureSet
import lang.Types.{NamedTypeShape, Type}
import lang.Visibility.Public

enum Device(val keyword: Keyword, val typeName: TypeIdentifier, val api: PredefApi) {
  
  case Console extends Device(Keyword.Console, NormalTypeId("Console"), ConsoleApi)
  case FileSystem extends Device(Keyword.Fs, NormalTypeId("FileSystem"), FileSystemApi)
  
  def tpe: Type = Type(NamedTypeShape(typeName), CaptureSet.singletonOfRoot, None)
  
  override def toString: String = keyword.str
}

object Device {
  
  val kwToDevice: Map[Keyword, Device] = values.map(d => d.keyword -> d).toMap
  
  val devicesTypes: Set[TypeIdentifier] = values.map(_.typeName).toSet
  
}
