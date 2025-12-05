package compiler.ssaprinter

import compiler.irs.SSA
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.valuesconversion.GlobalValuesContext
import lang.Values

final class SSAPrinter extends CompilerStep[Program, String] {

  override def apply(program: Program): String = {

    given pps: PrettyPrintString = PrettyPrintString(indentGranularity = 3)

    given globalValsCtx: GlobalValuesContext = program.globalValuesContext

    pps.newLine()
    for ((funSig, ssaFunc) <- program.functions) {
      pps.add(funSig.toString).addSpace().startBlock()
      ssaFunc.posOpt.foreach { position =>
        pps.add("/* src: ")
          .add(position.srcCodeProviderName)
          .add(" */")
          .newLine()
      }
      ssaFunc.bodyOpt match {
        case Some(body) =>
          addAllInstr(body, printIfEmpty = true)
        case None =>
          pps.add("/* abstract */")
      }
      pps.endBlock().newLine().newLine()
    }
    pps.built
  }

  private def add(instr: SSA.Instr)
                 (using pps: PrettyPrintString, globalValsCtx: GlobalValuesContext): Unit = {
    instr match {
      case SSA.Loop(cond, body, variables) =>
        pps.add("loop (").add(cond.toString).add(") ").startBlock()
        addAllInstr(body, printIfEmpty = true)
        pps.endBlock().add(" with vars ").startBlock()
        val varsIter = variables.iterator
        while (varsIter.hasNext) {
          val varInfo = varsIter.next()
          pps.add(varInfo.toString)
          if (varsIter.hasNext) {
            pps.newLine()
          }
        }
        pps.endBlock()
      case SSA.Disjunction(cond, thenBr, elseBr, postMerges) =>
        pps.add("if (").add(cond.toString).add(") ").startBlock()
        addAllInstr(thenBr, printIfEmpty = true)
        pps.endBlock().add(" else ").startBlock()
        addAllInstr(elseBr, printIfEmpty = true)
        pps.endBlock()
        if (postMerges.nonEmpty) pps.newLine()
        addAllInstr(postMerges, printIfEmpty = false)
      case SSA.Phi(assignedValue, inValues) =>
        pps.add(s"$assignedValue := phi ${inValues.mkString("{ ", ", ", " }")}")
      case SSA.Assignment(assignedValue, rhs) =>
        pps.add(assignedValue.toString).add(" := ").add(rhs.toString)
      case SSA.Instantiate(assignedValue, classOrStructName) =>
        pps.add(s"$assignedValue := new $classOrStructName")
      case SSA.Cast(assignedValue, inValue, targetType) =>
        pps.add(s"cast-dynamic $assignedValue := $inValue as $targetType")
      case SSA.StaticAssert(formula) =>
        pps.add(s"assert-static $formula")
      case SSA.StaticTypeAssert(value, tpe) =>
        pps.add(s"type-assert-static $value : $tpe")
      case SSA.FieldWrite(owner, fieldName, value) =>
        pps.add(s"$owner.$fieldName := $value")
      case SSA.Return(retVal) =>
        pps.add(s"return ").add(retVal.getOrElse("<void>").toString)
      case SSA.Panic(msg) =>
        pps.add("panic ").add(msg.toString)
      case SSA.Evaluate(formula) =>
        pps.add("evaluate ").add(formula.toString)
      case SSA.DynamicAssert(formula) =>
        pps.add(s"dynamic-assert $formula")
    }
  }

  private def addAllInstr(instructions: List[SSA.Instr], printIfEmpty: Boolean)
                         (using pps: PrettyPrintString, globalValsCtx: GlobalValuesContext): Unit = {
    if (printIfEmpty && instructions.isEmpty) {
      pps.add("/* empty */")
    }
    val iter = instructions.iterator
    while (iter.nonEmpty) {
      val instr = iter.next()
      add(instr)
      if (iter.nonEmpty) {
        pps.newLine()
      }
    }
  }

}
