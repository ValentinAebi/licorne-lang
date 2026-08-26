package compiler.backend

import compiler.lang.FunctionSignature
import compiler.lang.Types.NamedType
import compiler.stdlib.StdLib.*

import java.lang.classfile.MethodBuilder
import java.lang.constant.ConstantDescs.*
import java.lang.constant.MethodTypeDesc.of as javaSig
import java.lang.constant.{ClassDesc, MethodTypeDesc}

object StdLibFunctions {

  private val intrinsics = Map(
    (consoleTypeId, consolePrintFunId) -> generateConsolePrint,
    (consoleTypeId, consoleReadlineFunId) -> generateConsoleReadlLine
    // TODO FileWriter::write
  )
  
  private val stringFuncRedirect = Map(
    stringSizeFunId -> ("length", javaSig(CD_int)),
    stringConcatFunId -> ("concat", javaSig(CD_String, CD_String)),
    stringStartsWithFunId -> ("startsWith", javaSig(CD_boolean, CD_String)),
    stringEndsWithFunId -> ("endsWith", javaSig(CD_boolean, CD_String)),
    stringIndentFunId -> ("indent", javaSig(CD_String, CD_int)),
    stringJavaIndexOfFunId -> ("indexOf", javaSig(CD_int, CD_String)),
    stringJavaLastIndexOfFunId -> ("lastIndexOf", javaSig(CD_int, CD_String)),
    stringRepeatFunId -> ("repeat", javaSig(CD_String, CD_int)),
    stringReplaceFunId -> ("replace", javaSig(CD_String, CD_String, CD_String)),
    stringSubstringFunId -> ("substring", javaSig(CD_String, CD_int, CD_int)),
    stringToLowerCaseFunId -> ("toLowerCase", javaSig(CD_String)),
    stringToUpperCaseFunId -> ("toUpperCase", javaSig(CD_String))
  )

  def intrinsicFor(funSig: FunctionSignature): Option[MethodBuilder => Unit] = funSig.receiverType match {
    case NamedType(tid, _, _) =>
      intrinsics.get(tid, funSig.functionName)
    case _ => None
  }
  
  def stringFuncRedirectFor(sig: FunctionSignature): Option[(String, MethodTypeDesc)] = sig.receiverType match {
    case NamedType(tid, _, _) if tid == stringTypeId => stringFuncRedirect.get(sig.functionName)
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
