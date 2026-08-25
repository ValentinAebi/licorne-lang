package compiler.stdlib

import compiler.identifiers.{FunOrVarId, NormalFunOrVarId, TypeIdentifier}
import compiler.lang.FunctionSignature
import compiler.lang.Types.NamedType

object StdLib {

  def isFunc(recId: TypeIdentifier, funId: FunOrVarId)(sig: FunctionSignature): Boolean = sig.functionName == funId && (sig.receiverType match {
    case NamedType(tid, _, _) => tid == recId
    case _ => false
  })

  val stdLibPackageName: String = "licorne"

  private val licornePkgPrefix = List(stdLibPackageName)

  private val licorneCorePkgPrefix = licornePkgPrefix :+ "core"
  val indexedTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Indexed")
  val indexableTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Indexable")
  val sizeFunId: FunOrVarId = NormalFunOrVarId("size")
  val arrayTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Array")
  val arrayGetFunId: FunOrVarId = NormalFunOrVarId("get")
  val arraySetFunId: FunOrVarId = NormalFunOrVarId("set")
  val arrayLengthFunId: FunOrVarId = NormalFunOrVarId("length")
  val countTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Cnt")
  val indexTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Idx")
  val nonZeroIntTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "NonZeroInt")

  private val licorneIoPkgPrefix = licornePkgPrefix :+ "io"
  val consoleTypeId: TypeIdentifier = TypeIdentifier(licorneIoPkgPrefix, "Console")
  val consolePrintFunId: FunOrVarId = NormalFunOrVarId("print")
  val consolePrintlnFunId: FunOrVarId = NormalFunOrVarId("println")
  val consoleReadlineFunId: FunOrVarId = NormalFunOrVarId("readLine")

  private val licorneCollectionsPkgPrefix = licornePkgPrefix :+ "collections"

  private val licorneClosuresPkgPrefix = licornePkgPrefix :+ "closures"
  val heapVarTypeId: TypeIdentifier = TypeIdentifier(licorneClosuresPkgPrefix, "HeapVar")
  val intHeapVarTypeId: TypeIdentifier = TypeIdentifier(licorneClosuresPkgPrefix, "IntHeapVar")

  val automaticTypeImports: Iterable[(String, TypeIdentifier)] = List(
    // TODO add all type aliases from licorne.core
    nonZeroIntTypeId.nonPrefixedId -> nonZeroIntTypeId,
    countTypeId.nonPrefixedId -> countTypeId,
    indexTypeId.nonPrefixedId -> indexTypeId,
    arrayTypeId.nonPrefixedId -> arrayTypeId,
    indexedTypeId.nonPrefixedId -> indexedTypeId
  )

  val automaticFuncImports: Iterable[(FunOrVarId, (TypeIdentifier, FunOrVarId))] = List(
    consolePrintFunId -> (consoleTypeId, consolePrintFunId),
    consolePrintlnFunId -> (consoleTypeId, consolePrintlnFunId),
    consoleReadlineFunId -> (consoleTypeId, consoleReadlineFunId)
  )

}
