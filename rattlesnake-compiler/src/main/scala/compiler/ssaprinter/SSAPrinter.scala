package compiler.ssaprinter

import compiler.analysisctx.AnalysisContext
import compiler.irs.SSA
import compiler.pipeline.CompilerStep
import compiler.valuesconversion.GlobalValuesContext
import lang.{FunctionSignature, Values}

final class SSAPrinter extends CompilerStep[(Map[FunctionSignature, SSA.Function], AnalysisContext), String] {

  override def apply(input: (Map[FunctionSignature, SSA.Function], AnalysisContext)): String = {
    val (functions, analysisCtx) = input

    given pps: PrettyPrintString = PrettyPrintString(indentGranularity = 3)

    given globalValsCtx: GlobalValuesContext = analysisCtx.globalValuesContext

    for ((funSig, ssaFunc) <- functions) {
      pps.add(funSig.toString).addSpace().startBlock()
      ssaFunc.codeProviderNameOpt.foreach { srcFileName =>
        pps.add("/* src: ").add(srcFileName).add(" */")
      }
      pps.newLine().add("/* ")
      for (paramVal <- funSig.paramsInclThis.keys) {
        globalValsCtx.debugInfoOf(paramVal)
          .flatMap(_.referencedLocal)
          .foreach { localId =>
            pps.add(paramVal.toString).add("=").add(localId).add(" ")
          }
      }
      pps.add(" */").newLine()
      addAllInstr(ssaFunc.body, printIfEmpty = true)
      pps.endBlock().newLine().newLine()
    }
    pps.built
  }

  private def add(instr: SSA.Instr)
                 (using pps: PrettyPrintString, globalValsCtx: GlobalValuesContext): Unit = {
    instr match {
      case SSA.Loop(preBodyCond, cond, body, postMerges) =>
        pps.add("loop ").startBlock()
        addAllInstr(preBodyCond, printIfEmpty = true)
        pps.endBlock().add(" (").add(cond.toString).add(") ").startBlock()
        addAllInstr(body, printIfEmpty = true)
        pps.endBlock()
        if (postMerges.nonEmpty) pps.newLine()
        addAllInstr(postMerges, printIfEmpty = false)
      case SSA.Disjunction(cond, thenBr, elseBr, postMerges) =>
        pps.add("if (").add(cond.toString).add(") ").startBlock()
        addAllInstr(thenBr, printIfEmpty = true)
        pps.endBlock().add(" else ").startBlock()
        addAllInstr(elseBr, printIfEmpty = true)
        pps.endBlock()
        if (postMerges.nonEmpty) pps.newLine()
        addAllInstr(postMerges, printIfEmpty = false)
      case SSA.RegPhi(assignedValue, inValues) =>
        pps.add(s"$assignedValue := phi ${inValues.mkString("{ ", ", ", " }")}")
      case SSA.LoopIterPhi(assignedValue, baseCaseValue, prevIterValue) =>
        pps.add(s"$assignedValue := phi { $baseCaseValue (base), $prevIterValue (previous) }")
      case SSA.LoopExitPhi(assignedValue, bodyEndValue, skipLoopValue) =>
        pps.add(s"$assignedValue := phi { $bodyEndValue (loop) or $skipLoopValue (skip) }")
      case SSA.Assignment(assignedValue, rhs) =>
        pps.add(assignedValue.toString).add(" := ").add(rhs.toString)
      case SSA.Instantiate(assignedValue, classOrStructName) => ???
      case SSA.Cast(assignedValue, inValue, targetType) => ???
      case SSA.StaticTypeAssert(value, tpe) =>
        pps.add(s"type-assert $value : $tpe")
      case SSA.FieldWrite(owner, fieldName, value) =>
        pps.add(s"$owner.$fieldName := $value")
      case SSA.Return(retVal) =>
        pps.add(s"return ").add(retVal.getOrElse("<void>").toString)
      case SSA.Panic(msg) =>
        pps.add("panic ").add(msg.toString)
      case SSA.Evaluate(formula) =>
        pps.add("evaluate ").add(formula.toString)
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
      addDebugInfo(instr)
      if (iter.nonEmpty) {
        pps.newLine()
      }
    }
  }

  private def addDebugInfo(instr: SSA.Instr)(using pps: PrettyPrintString, globalValsCtx: GlobalValuesContext): Unit = {
    val sb = StringBuilder()
    instr match {
      case assigningInstr: SSA.AssigningInstr =>
        globalValsCtx.debugInfoOf(assigningInstr.assignedValue)
          .flatMap(_.referencedLocal)
          .foreach { debugInfo =>
            sb.append(" /* ").append(assigningInstr.assignedValue).append("=").append(debugInfo).append(" */")
          }
      case _ => ()
    }
    instr.getAstNodeOpt
      .flatMap(_.getPosition)
      .foreach { pos =>
        sb.append(s" /* ${pos.line}:${pos.col} */")
      }
    if (sb.nonEmpty) {
      pps.add("   ").add(sb.toString())
    }
  }

}
