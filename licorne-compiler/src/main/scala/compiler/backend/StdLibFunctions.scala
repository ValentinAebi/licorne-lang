package compiler.backend

import compiler.identifiers.{FunOrVarId, TypeIdentifier}
import compiler.lang.FunctionSignature
import compiler.lang.Types.NamedType
import compiler.stdlib.StdLib.*

import java.lang.classfile.MethodBuilder
import java.lang.constant.ConstantDescs.*
import java.lang.constant.{ClassDesc, MethodTypeDesc}

object StdLibFunctions {

  private val intrinsics: Map[(TypeIdentifier, FunOrVarId), MethodBuilder => Unit] = Map(
    (consoleTypeId, consolePrintFunId) -> generateConsolePrint,
    (consoleTypeId, consoleReadlineFunId) -> generateConsoleReadlLine
    // TODO FileWriter::write
  )

  def intrinsicFor(funSig: FunctionSignature): Option[MethodBuilder => Unit] = funSig.receiverType match {
    case NamedType(tid, _, _) =>
      intrinsics.get(tid, funSig.functionName)
    case _ => None
  }

  private def generateConsolePrint(mb: MethodBuilder): Unit = mb.withCode(cb => {
    val systemDesc = ClassDesc.of("java.lang.System")
    val printStreamDesc = ClassDesc.of("java.io.PrintStream")
    cb.getstatic(systemDesc, "out", printStreamDesc)
    cb.aload(1)
    cb.invokevirtual(printStreamDesc, "print", MethodTypeDesc.of(CD_void, CD_Object))
    cb.return_()
  })

  private def generateConsoleReadlLine(mb: MethodBuilder): Unit = mb.withCode(cb => {
    val systemDesc = ClassDesc.of("java.lang.System")
    val javaConsoleDesc = ClassDesc.of("java.io.Console")
    cb.invokestatic(systemDesc, "console", MethodTypeDesc.of(javaConsoleDesc))
    cb.invokevirtual(javaConsoleDesc, "readLine", MethodTypeDesc.of(CD_String))
    cb.areturn()
  })

}
