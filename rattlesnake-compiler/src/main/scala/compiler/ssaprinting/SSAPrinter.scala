package compiler.ssaprinting

import compiler.irs.SSA
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.typechecking.TypeStore
import compiler.valuesconversion.GlobalValuesContext
import lang.Types.Type
import lang.Values
import lang.Values.IdValue

final class SSAPrinter[T](
                           private val getProgram: T => Program,
                           private val getTypeStore: T => Option[TypeStore]
                         ) extends CompilerStep[T, String] {

  override def apply(input: T): String = {
    val program = getProgram(input)
    val tsOpt = getTypeStore(input)

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
          addAllInstr(body, printIfEmpty = true)(using tsOpt.map(_.typeOfOpt).getOrElse(_ => None))
        case None =>
          pps.add("/* abstract */")
      }
      pps.endBlock().newLine().newLine()
    }
    pps.built
  }

  private def add(instr: SSA.Instr)
                 (using typeFunc: IdValue => Option[Type], pps: PrettyPrintString, globalValsCtx: GlobalValuesContext): Unit = {
    instr match {
      case SSA.Loop(cond, body, variables) =>
        pps.add("loop (").add(cond.str).add(") ").startBlock()
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
        pps.add("if (").add(cond.str).add(") ").startBlock()
        addAllInstr(thenBr, printIfEmpty = true)
        pps.endBlock().add(" else ").startBlock()
        addAllInstr(elseBr, printIfEmpty = true)
        pps.endBlock()
        if (postMerges.nonEmpty) pps.newLine()
        addAllInstr(postMerges, printIfEmpty = false)
      case SSA.Phi(assignedValue, inValues) =>
        pps.add(s"${assignedValue.str} := phi ${inValues.map(_.str).mkString("{ ", ", ", " }")}")
      case SSA.Assignment(assignedValue, rhs) =>
        pps.add(assignedValue.str).add(" := ").add(rhs.str)
      case SSA.Instantiate(assignedValue, classOrRecordName, typeArgs, initialization) =>
        pps.add(s"${assignedValue.str} := new $classOrRecordName")
        if (typeArgs.nonEmpty) {
          pps.add("[")
          val tArgsIter = typeArgs.iterator
          while (tArgsIter.hasNext) {
            pps.add(tArgsIter.next().toString)
            if (tArgsIter.hasNext) {
              pps.add(",")
            }
          }
          pps.add("]")
        }
        if (initialization.nonEmpty) {
          pps.addSpace().startBlock()
        }
        addAllInstr(initialization, printIfEmpty = false)
        if (initialization.nonEmpty) {
          pps.endBlock()
        }
      case SSA.Cast(inValue, targetType) =>
        pps.add(s"cast-dynamic ${inValue.str} as $targetType")
      case SSA.Conversion(assignedValue, inValue, targetType) =>
        pps.add(s"convert ${assignedValue.str} := ${inValue.str} as $targetType")
      case SSA.StaticAssert(formula) =>
        pps.add(s"assert-static ${formula.str}")
      case SSA.StaticTypeAssert(value, tpe) =>
        pps.add(s"type-assert-static $value : $tpe")
      case SSA.FieldWrite(owner, fieldName, value) =>
        pps.add(s"${owner.str}.$fieldName := ${value.str}")
      case SSA.Return(retVal) =>
        pps.add(s"return ").add(retVal.map(_.str).getOrElse("<void>"))
      case SSA.Panic(msg) =>
        pps.add("panic ").add(msg.str)
      case SSA.Evaluate(formula) =>
        pps.add("evaluate ").add(formula.str)
      case SSA.DynamicAssert(formula) =>
        pps.add(s"dynamic-assert ${formula.str}")
      case SSA.LocalDecl(localId, tpe) =>
        pps.add(s"decl-local $localId : $tpe")
      case SSA.ClosureCreation(assignedValue, params, body) =>
        pps.add(s"new-closure $assignedValue (")
        val paramsIter = params.iterator
        while (paramsIter.hasNext){
          val (paramVal, paramType) = paramsIter.next()
          pps.add(s"$paramVal: $paramType")
          if (paramsIter.hasNext){
            pps.add(", ")
          }
        }
        pps.add(") -> ").startBlock()
        addAllInstr(body, printIfEmpty = true)
        pps.endBlock()
    }
  }

  private def addAllInstr(instructions: List[SSA.Instr], printIfEmpty: Boolean)
                         (using typeFunc: IdValue => Option[Type], pps: PrettyPrintString, globalValsCtx: GlobalValuesContext): Unit = {
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

object SSAPrinter {

  def apply[T](getProgram: T => Program, getTypeStore: T => TypeStore): SSAPrinter[T] = {
    new SSAPrinter(getProgram, t => Some(getTypeStore(t)))
  }

}
