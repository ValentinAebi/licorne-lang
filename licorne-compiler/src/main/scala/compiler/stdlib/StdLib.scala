package compiler.stdlib

import compiler.identifiers.{FunOrVarId, NormalFunOrVarId, TypeIdentifier}
import compiler.lang.FunctionSignature
import compiler.lang.Types.NamedType

object StdLib {
  
  def hasReceiver(recId: TypeIdentifier)(sig: FunctionSignature): Boolean = sig.receiverType match {
    case NamedType(tid, _, _) => tid == recId
    case _ => false
  }

  def isFunc(recId: TypeIdentifier, funId: FunOrVarId)(sig: FunctionSignature): Boolean =
    hasReceiver(recId)(sig) && sig.functionName == funId

  val stdLibPackageName: String = "licorne"

  val licornePkgPrefix: List[String] = List(stdLibPackageName)

  // licorne.core
  val licorneCorePkgPrefix: List[String] = licornePkgPrefix :+ "core"
  val indexedTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Indexed")
  val indexableTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Indexable")
  val sizeFunId: FunOrVarId = NormalFunOrVarId("size")
  val arrayTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Array")
  val arrayGetFunId: FunOrVarId = NormalFunOrVarId("get")
  val arraySetFunId: FunOrVarId = NormalFunOrVarId("set")
  val arraySizeFunId: FunOrVarId = NormalFunOrVarId("size")
  val countTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Cnt")
  val indexTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "Idx")
  val nonZeroIntTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "NonZeroInt")

  // licorne.core.String
  val stringTypeId: TypeIdentifier = TypeIdentifier(licorneCorePkgPrefix, "String")
  val stringType: NamedType = NamedType(StdLib.stringTypeId, List.empty, List.empty)
  val stringSizeFunId: FunOrVarId = NormalFunOrVarId("size")
  val stringIsEmptyFunId: FunOrVarId = NormalFunOrVarId("isEmpty")
  val stringConcatFunId: FunOrVarId = NormalFunOrVarId("concat")
  val stringStartsWithFunId: FunOrVarId = NormalFunOrVarId("startsWith")
  val stringEndsWithFunId: FunOrVarId = NormalFunOrVarId("endsWith")
  val stringIndentFunId: FunOrVarId = NormalFunOrVarId("indent")
  val stringRepeatFunId: FunOrVarId = NormalFunOrVarId("repeat")
  val stringReplaceFunId: FunOrVarId = NormalFunOrVarId("replace")
  val stringSubstringFunId: FunOrVarId = NormalFunOrVarId("substring")
  val stringToUpperCaseFunId: FunOrVarId = NormalFunOrVarId("toUpperCase")
  val stringToLowerCaseFunId: FunOrVarId = NormalFunOrVarId("toLowerCase")
  val stringJavaIndexOfFunId: FunOrVarId = NormalFunOrVarId("javaIndexOf")
  val stringJavaLastIndexOfFunId: FunOrVarId = NormalFunOrVarId("javaLastIndexOf")

  // licorne.io
  val licorneIoPkgPrefix: List[String] = licornePkgPrefix :+ "io"
  val consoleTypeId: TypeIdentifier = TypeIdentifier(licorneIoPkgPrefix, "Console")
  val consolePrintFunId: FunOrVarId = NormalFunOrVarId("print")
  val consolePrintlnFunId: FunOrVarId = NormalFunOrVarId("println")
  val consoleReadlineFunId: FunOrVarId = NormalFunOrVarId("readLine")

  // licorne.collections
  val licorneCollectionsPkgPrefix: List[String] = licornePkgPrefix :+ "collections"

  // licorne.closures
  val licorneClosuresPkgPrefix: List[String] = licornePkgPrefix :+ "closures"
  val heapVarTypeId: TypeIdentifier = TypeIdentifier(licorneClosuresPkgPrefix, "HeapVar")
  val heapVarGetFunId: FunOrVarId = NormalFunOrVarId("get")
  val heapVarSetFunId: FunOrVarId = NormalFunOrVarId("set")

  val automaticTypeImports: Iterable[(String, TypeIdentifier)] = List(
    // TODO add all type aliases from licorne.core
    nonZeroIntTypeId.nonPrefixedId -> nonZeroIntTypeId,
    countTypeId.nonPrefixedId -> countTypeId,
    indexTypeId.nonPrefixedId -> indexTypeId,
    arrayTypeId.nonPrefixedId -> arrayTypeId,
    indexedTypeId.nonPrefixedId -> indexedTypeId,
    indexableTypeId.nonPrefixedId -> indexableTypeId,
    stringTypeId.nonPrefixedId -> stringTypeId
  )

  val automaticFuncImports: Iterable[(FunOrVarId, (TypeIdentifier, FunOrVarId))] = List(
    consolePrintFunId -> (consoleTypeId, consolePrintFunId),
    consolePrintlnFunId -> (consoleTypeId, consolePrintlnFunId),
    consoleReadlineFunId -> (consoleTypeId, consoleReadlineFunId)
  )

}
