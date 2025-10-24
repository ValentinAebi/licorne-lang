package compiler.prettyprinter

import compiler.irs.Asts.*
import compiler.pipeline.CompilerStep
import lang.Keyword.*
import lang.{Keyword, Operator, Visibility}

final class PrettyPrinter(indentGranularity: Int = 2, displayAllParentheses: Boolean = false) extends CompilerStep[Ast, String] {

  override def apply(input: Ast): String = {
    val pps = new PrettyPrintString(indentGranularity)
    addAst(input)(pps)
    pps.built
  }

  private def addAst(ast: Ast)(implicit pps: PrettyPrintString): Unit = {
    ast match {

      case Source(defs) =>
        pps.newLine()
        for df <- defs do {
          pps.newLine()
          addAst(df)
          pps.newLine()
        }

      case Block(stats) =>
        addBracesList(stats, ";", onMultipleLines = true)

      case Sequence(stats, expr) =>
        addBracesList(stats :+ expr, ";", onMultipleLines = true)

      case ModuleDef(moduleName, imports, functions) =>
        pps
          .add(Module.str)
          .addSpace()
          .add(moduleName)
        addParenthList(imports)
        pps
          .add(" {")
          .incrementIndent()
          .newLine()
        for (func <- functions) {
          pps.newLine()
          addAst(func)
          pps.newLine()
        }
        pps
          .decrementIndent()
          .newLine()
          .add("}")

      case PackageDef(packageName, functions) =>
        pps
          .add(Package.str)
          .addSpace()
          .add(packageName)
          .add(" {")
          .incrementIndent()
          .newLine()
        for (func <- functions) {
          pps.newLine()
          addAst(func)
          pps.newLine()
        }
        pps
          .decrementIndent()
          .newLine()
          .add("}")

      case FunDef(funName, args, optRetTypeTree, body, visibility, isMain) =>
        if (visibility.isPrivate){
          pps
            .add(Keyword.Private.str)
            .addSpace()
        }
        if (isMain){
          pps
            .add(Main.str)
            .addSpace()
        }
        pps
          .add(Fn.str)
          .addSpace()
          .add(funName)
        addParenthList(args)
        optRetTypeTree.foreach { retTypeTree =>
          pps.add(" -> ")
          addAst(retTypeTree)
          pps.addSpace()
        }
        addAst(body)

      case StructDef(structName, fields, directSupertypes, isAbstract) =>
        pps
          .add(if isAbstract then Datatype.str else Struct.str)
          .addSpace()
          .add(structName)
          .addSpace()
        if (directSupertypes.nonEmpty){
          pps.add(": ")
          val iter = directSupertypes.iterator
          while (iter.hasNext){
            pps.add(iter.next())
            if (iter.hasNext){
              pps.add(", ")
            }
          }
        }
        if (fields.nonEmpty) {
          addBracesList(fields, ",", onMultipleLines = true)
        }

      case ConstDef(constName, typeTreeOpt, value) =>
        pps
          .add(Const.str)
          .addSpace()
          .add(constName)
        typeTreeOpt.foreach { typeTree =>
          pps.add(": ")
          addAst(typeTree)
        }
        pps.add(" = ")
        addAst(value)

      case Param(paramNameOpt, typeTree, isReassignable) =>
        if (isReassignable){
          pps
            .add(Var.str)
            .addSpace()
        }
        paramNameOpt.foreach { paramName =>
          pps.add(paramName).add(": ")
        }
        addAst(typeTree)

      case ParamImport(paramName, paramTypeTree) =>
        pps
          .add(paramName)
          .add(": ")
        addAst(paramTypeTree)

      case PackageImport(packageId) =>
        pps
          .add(Package.str)
          .addSpace()
          .add(packageId)

      case DeviceImport(device) =>
        pps
          .add(Keyword.Device.str)
          .addSpace()
          .add(device.keyword.str)

      case localDef@LocalDef(valName, optTypeTree, rhsOpt, isReassignable) =>
        pps
          .add(localDef.keyword.str)
          .addSpace()
          .add(valName)
        optTypeTree.foreach { typeTree =>
          pps.add(": ")
          addAst(typeTree)
        }
        pps.add(" = ")
        rhsOpt.foreach(addAst(_))

      case IntLit(value) =>
        pps.add(value.toString)

      case DoubleLit(value) =>
        pps.add(value.toString)

      case CharLit(value) =>
        pps
          .add("'")
          .add(if value == '\n' then "\\n" else value.toString)
          .add("'")

      case BoolLit(value) =>
        pps.add(value.toString)

      case StringLit(value) =>
        pps
          .add("\"")
          .add(value.replace("\n", "\\n"))
          .add("\"")

      case VariableRef(name) =>
        pps.add(name)

      case MeRef() =>
        pps.add(Me.str)

      case PackageRef(pkgName) =>
        pps.add(pkgName)

      case DeviceRef(device) =>
        pps.add(device.keyword.str)

      case Call(receiverOpt, funName, args, isTailrec) =>
        receiverOpt.foreach { recv =>
          addAst(recv)
          pps.add(".")
        }
        pps.add(funName)
        if (isTailrec){
          pps.add(Operator.ExclamationMark.str)
        }
        addParenthList(args)

      case Indexing(indexed, arg) =>
        addAst(indexed)
        pps.add("[")
        addAst(arg)
        pps.add("]")

      case ArrayInit(elemTypeTree, size) =>
        pps.add(Arr.str)
        pps.addSpace()
        addAst(elemTypeTree)
        pps.add("[")
        addAst(size)
        pps.add("]")

      case FilledArrayInit(arrayElems) =>
        addParenthList(arrayElems, parenth = ("[", "]"))

      case StructOrModuleInstantiation(structName, args) =>
        pps
          .add(New.str)
          .addSpace()
        pps.add(structName)
        addParenthList(args)

      case UnaryOp(operator, operand) =>
        pps.add(operator.str)
        if (operator.isNamedOperator){
          pps.addSpace()
        }
        val displayParenth = operand.isInstanceOf[UnaryOp | BinaryOp]
        if (displayParenth) {
          pps.add("(")
        }
        addAst(operand)
        if (displayParenth) {
          pps.add(")")
        }

      case BinaryOp(lhs, operator, rhs) =>
        val displayParenthLeft = parenthesesNeededLeft(operator, lhs, displayAllParentheses)
        if (displayParenthLeft) {
          pps.add("(")
        }
        addAst(lhs)
        if (displayParenthLeft) {
          pps.add(")")
        }
        pps
          .addSpace()
          .add(operator.str)
          .addSpace()
        val displayParenthRight = parenthesesNeededRight(operator, rhs, displayAllParentheses)
        if (displayParenthRight) {
          pps.add("(")
        }
        addAst(rhs)
        if (displayParenthRight) {
          pps.add(")")
        }

      case Select(lhs, selected) =>
        addAst(lhs)
        pps
          .add(".")
          .add(selected)

      case VarAssig(lhs, rhs) =>
        addAst(lhs)
        pps.add(" = ")
        addAst(rhs)

      case VarModif(lhs, rhs, op) =>
        addAst(lhs)
        pps
          .addSpace()
          .add(op.str)
          .add("=")
          .addSpace()
        addAst(rhs)

      case IfThenElse(cond, thenBr, elseBrOpt) =>
        pps
          .add(If.str)
          .addSpace()
        addCond(cond)
        pps.addSpace()
        addAst(thenBr)
        elseBrOpt.foreach { elseBr =>
          pps
            .addSpace()
            .add(Else.str)
            .addSpace()
          addAst(elseBr)
        }

      case Ternary(cond, thenBr, elseBr) =>
        pps
          .add(When.str)
          .addSpace()
        addCond(cond)
        pps
          .addSpace()
          .add(Then.str)
          .addSpace()
        addAst(thenBr)
        pps
          .addSpace()
          .add(Else.str)
          .addSpace()
        addAst(elseBr)

      case WhileLoop(cond, body) =>
        pps
          .add(While.str)
          .addSpace()
        addCond(cond)
        pps.addSpace()
        addAst(body)

      case ForLoop(initStats, cond, stepStats, body) =>
        pps
          .add(For.str)
          .addSpace()
        val initStatsIter = initStats.iterator
        while (initStatsIter.hasNext) {
          addAst(initStatsIter.next())
          if (initStatsIter.hasNext) {
            pps.add(", ")
          }
        }
        pps.add("; ")
        addAst(cond)
        pps.add("; ")
        val stepStatsIter = stepStats.iterator
        while (stepStatsIter.hasNext) {
          addAst(stepStatsIter.next())
          if (stepStatsIter.hasNext) {
            pps.add(", ")
          }
        }
        pps.addSpace()
        addAst(body)

      case ReturnStat(valueOpt) =>
        pps.add(Return.str)
        valueOpt.foreach { value =>
          pps.addSpace()
          addAst(value)
        }

      case Cast(expr, tpe) =>
        addAst(expr)
        pps
          .addSpace()
          .add(As.str)
          .addSpace()
        addAst(tpe)

      case TypeTest(expr, tpe) =>
        addAst(expr)
        pps
          .addSpace()
          .add(Is.str)
          .addSpace()
        addAst(tpe)

      case PanicStat(msg) =>
        pps
          .add(Panic.str)
          .addSpace()
        addAst(msg)

      case CapturingTypeTree(ArrayTypeShapeTree(elemType), captureDescr) =>
        addArrayTypeTree(elemType, Some(captureDescr))

      case CapturingTypeTree(typeShapeTree, captureDescr) =>
        addAst(typeShapeTree)
        pps.add("^")
        addAst(captureDescr)

      case WrapperTypeTree(tpe) =>
        pps.add(tpe.toString)

      case ArrayTypeShapeTree(elemTypeTree) =>
        addArrayTypeTree(elemTypeTree, arrayCdTreeOpt = None)

      case PrimitiveTypeShapeTree(primitiveType) =>
        pps.add(primitiveType.toString)

      case NamedTypeShapeTree(name) =>
        pps.add(name)

      case ExplicitCaptureSetTree(capturedExpressions) =>
        addBracesList(capturedExpressions, ",", onMultipleLines = false)

      case ImplicitRootCaptureSetTree() => ()

    }
  }

  private def addArrayTypeTree(elemTypeTree: TypeTree, arrayCdTreeOpt: Option[CaptureSetTree])
                              (implicit pps: PrettyPrintString): Unit = {
    pps.add(Arr.str)
    arrayCdTreeOpt.foreach { arrayCdTree =>
      pps.add("^")
      addAst(arrayCdTree)
    }
    pps.addSpace()
    addAst(elemTypeTree)
  }

  private def addCond(cond: Expr)(implicit pps: PrettyPrintString): Unit = {
    if (displayAllParentheses) {
      pps.add("(")
    }
    addAst(cond)
    if (displayAllParentheses) {
      pps.add(")")
    }
  }

  private def parenthesesNeededLeft(externalOp: Operator, leftOperand: Expr, displayAllParentheses: Boolean): Boolean = {
    leftOperand match
      case _: UnaryOp => displayAllParentheses
      case BinaryOp(_, operator, _) =>
        displayAllParentheses || Operator.priorities(operator) < Operator.priorities(externalOp)
      case _ => false
  }

  private def parenthesesNeededRight(externalOp: Operator, rightOperand: Expr, displayAllParentheses: Boolean): Boolean = {
    rightOperand match
      case UnaryOp(operator, _) =>
        displayAllParentheses || operator == Operator.Minus
      case BinaryOp(_, operator, _) =>
        displayAllParentheses || Operator.priorities(operator) <= Operator.priorities(externalOp)
      case _ => false
  }

  private def addBracesList(ls: List[Ast], sep: String, onMultipleLines: Boolean)(implicit pps: PrettyPrintString): Unit = {
    val iter = ls.iterator
    if (onMultipleLines) {
      pps
        .startBlock()
        .newLine()
    } else {
      pps.add("{")
    }
    while (iter.hasNext) {
      addAst(iter.next())
      if (iter.hasNext) {
        pps.add(sep)
        if (onMultipleLines) {
          pps.newLine()
        }
      }
    }
    if (onMultipleLines) {
      pps.endBlock()
    }
    else {
      pps.add("}")
    }
  }

  private def addParenthList(ls: List[Ast], parenth: (String, String) = ("(", ")"))(implicit pps: PrettyPrintString): Unit = {
    val iter = ls.iterator
    pps.add(parenth._1)
    while (iter.hasNext) {
      addAst(iter.next())
      if (iter.hasNext) {
        pps.add(", ")
      }
    }
    pps.add(parenth._2)
  }

}
