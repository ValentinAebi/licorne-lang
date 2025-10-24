package compiler.importscanner

import compiler.irs.Asts.{DeviceImport, ModuleDef, PackageImport}
import identifiers.TypeIdentifier
import lang.Device

final case class ModuleImports(packages: List[TypeIdentifier], devices: List[Device])

object ModuleImports {
  
  def fromModuleDef(moduleDef: ModuleDef): ModuleImports = ModuleImports(
    moduleDef.imports.flatMap {
      case PackageImport(packageId) => Some(packageId)
      case _ => None
    },
    moduleDef.imports.flatMap {
      case DeviceImport(device) => Some(device)
      case _ => None
    }
  )
  
}
