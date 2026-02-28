package compiler.display

import compiler.identifiers.FunOrVarId
import compiler.irs.SSA
import compiler.irs.SSA.*
import compiler.lang.Formulas.{IdValue, NamedIdValue}
import compiler.lang.Types.{NamedType, Type}
import compiler.lang.{ClassSignature, DatatypeSignature, Field, Formulas, FunctionSignature, InterfaceSignature, ObjectSignature, RecordSignature, TypeAliasSignature, TypeParamInfo, Types}
import compiler.pipeline.CompilerStep
import compiler.program.Program
import compiler.reporting.Position

import java.util.stream.Collectors

final class SSAPrinter(indentUnit: String) extends CompilerStep[Program, String] {

  override def apply(program: Program): String = {
    given Program = program

    given pps: PrettyPrintString = PrettyPrintString(indentUnit)

    for ((_, sig) <- program.typeAliases) {
      printTypeAlias(sig)
    }
    for ((_, sig) <- program.interfaces) {
      printInterface(sig)
    }
    for ((_, sig) <- program.classes) {
      printClass(sig)
    }
    for ((_, sig) <- program.objects) {
      printObject(sig)
    }
    for ((_, sig) <- program.datatypes) {
      printDatatype(sig)
    }
    for ((_, sig) <- program.records) {
      printRecord(sig)
    }

    pps.built
  }

  private def printTypeAlias(typealiasSig: TypeAliasSignature)
                            (using pps: PrettyPrintString, program: Program): Unit = {
    val TypeAliasSignature(id, typeParams, idValue, params, rhs, declPosOpt) = typealiasSig
    pps.add("TYPEALIAS").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
      .add(mkTypeAliasParamsDescr(params))
      .add(" = ").add(rhs)
      .add(mkPosDescr(declPosOpt))
      .newLine()
  }

  private def printInterface(interfaceSig: InterfaceSignature)
                            (using pps: PrettyPrintString, program: Program): Unit = {
    val InterfaceSignature(id, typeParams, functions, directSupertypes, declPosOpt) = interfaceSig
    pps.add("INTERFACE").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
      .add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions)
    pps.newLine()
  }

  private def printClass(classSig: ClassSignature)
                        (using pps: PrettyPrintString, program: Program): Unit = {
    val ClassSignature(id, typeParams, fields, functions, directSupertypes, declPosOpt) = classSig
    pps.add("CLASS").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
    printFields(fields)
    pps.add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions)
    pps.newLine()
  }

  private def printObject(objectSig: ObjectSignature)
                         (using pps: PrettyPrintString, program: Program): Unit = {
    val ObjectSignature(id, functions, directSupertypes, declPosOpt) = objectSig
    pps.add("OBJECT").addSpace().add(id)
      .add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
    printFunctionsBlockIfNotEmpty(functions)
    pps.newLine()
  }

  private def printDatatype(datatypeSig: DatatypeSignature)
                           (using pps: PrettyPrintString): Unit = {
    val DatatypeSignature(id, typeParams, directSupertypes, directSubtypes, declPosOpt) = datatypeSig
    pps.add("DATATYPE").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
      .add(mkSuperTypesDescr(directSupertypes))
      .add(" with cases ")
    traverseIterable(directSubtypes.iterator) { subT =>
      pps.add(subT)
    } {
      pps.add(", ")
    }
    pps.add(mkPosDescr(declPosOpt)).newLine()
  }

  private def printRecord(recordSig: RecordSignature)
                         (using pps: PrettyPrintString): Unit = {
    val RecordSignature(id, typeParams, fields, directSupertypes, declPosOpt) = recordSig
    pps.add("RECORD").addSpace().add(id)
      .add(mkTypeParamsDescr(typeParams))
    printFields(fields)
    pps.add(mkSuperTypesDescr(directSupertypes))
      .add(mkPosDescr(declPosOpt))
      .newLine()
  }

  private def printFunctionsBlockIfNotEmpty(functions: Map[FunOrVarId, FunctionSignature])
                                           (using pps: PrettyPrintString, program: Program): Unit = {
    if (functions.nonEmpty) {
      pps.addSpace().block {
        for ((_, funSig) <- functions) {
          printFunction(funSig)
        }
      }
    }
  }

  private def printFunction(funSig: FunctionSignature)
                           (using pps: PrettyPrintString, program: Program): Unit = {
    val FunctionSignature(ownerName, functionName, typeParams, paramsInclThis, retType, visibility, declPosOpt) = funSig
    pps.add(s"METHOD ($visibility) $ownerName::$functionName${mkTypeParamsDescr(typeParams)}${mkFunctionParamsDescr(paramsInclThis)} -> $retType${mkPosDescr(declPosOpt)}")
    program.functions.get(funSig)
      .flatMap(_.bodyOpt)
      .foreach { funBody =>
        printScope(funBody)
      }
  }

  private def printScope(scope: Scope)(using pps: PrettyPrintString): Unit = {
    pps.add(s"SCOPE").addSpace().add(scope.scopeUid).addSpace().block {
      traverseIterable(scope.instructions.iterator) { instr =>
        printInstr(instr)
      } {
        pps.newLine()
      }
    }.newLine()
  }

  private def printFields(fields: Iterable[(FunOrVarId, Field)])
                         (using pps: PrettyPrintString): Unit = {
    fields.size match {
      case 0 => ()
      case 1 =>
        val (_, fld) = fields.head
        pps.add("(").add(fld.toString).add(")")
      case _ =>
        pps.add("(").indent {
          traverseIterable(fields.iterator) { (_, fld) =>
            pps.add(fld.toString)
          } {
            pps.add(",").newLine()
          }
        }.add(")")
    }
  }

  private def printInstr(instr: Instr)(using pps: PrettyPrintString): Unit = instr match {
    case SSA.Loop(cond, condVal, body, variables) =>
      pps.add("LOOP").addSpace().indent {
        printVarData(variables)
        pps.add(s"cond [as $condVal]: ")
        printScope(cond)
        pps.add("body: ")
        printScope(body)
      }
      pps.add("END LOOP")
    case SSA.Disjunction(condVal, thenBr, elseBr, variables) =>
      pps.add("IF [cond = ").add(condVal).add("]").indent {
        printVarData(variables)
        pps.add("then: ")
        printScope(thenBr)
        pps.add("else: ")
        printScope(elseBr)
      }
      pps.add("END IF")
    case SSA.StaticTypeAssert(value, tpe) =>
      pps.add(s"TYPE-ASSERT $value : $tpe")
    case SSA.StaticAssert(value) =>
      pps.add(s"ASSERT $value")
    case AssignVal(assigned, src) =>
      pps.add(s"ASSIG $assigned := $src")
    case AssignIntConst(assigned, src) =>
      pps.add(s"INTC $assigned := $src")
    case AssignBoolConst(assigned, src) =>
      pps.add(s"BOOLC $assigned := $src")
    case AssignStringConst(assigned, src) =>
      pps.add(s"STRINGC $assigned := $src")
    case NumNeg(assigned, operand) =>
      pps.add(s"NEG $assigned := -$operand")
    case Add(assigned, lhs, rhs) =>
      pps.add(s"ADD $assigned := $lhs + $rhs")
    case Sub(assigned, lhs, rhs) =>
      pps.add(s"SUB $assigned := $lhs - $rhs")
    case Mul(assigned, lhs, rhs) =>
      pps.add(s"MUL $assigned := $lhs * $rhs")
    case Div(assigned, lhs, rhs) =>
      pps.add(s"DIV $assigned := $lhs / $rhs")
    case Rem(assigned, lhs, rhs) =>
      pps.add(s"REM $assigned := $lhs % $rhs")
    case LogicNeg(assigned, operand) =>
      pps.add(s"NOT $assigned := !$operand")
    case And(assigned, lhs, rhs) =>
      pps.add(s"AND $assigned := $lhs & $rhs")
    case Or(assigned, lhs, rhs) =>
      pps.add(s"OR $assigned := $lhs | $rhs")
    case Equal(assigned, lhs, rhs) =>
      pps.add(s"EQ $assigned := $lhs == $rhs")
    case Leq(assigned, lhs, rhs) =>
      pps.add(s"LEQ $assigned := $lhs <= $rhs")
    case Lt(assigned, lhs, rhs) =>
      pps.add(s"LT $assigned := $lhs < $rhs")
    case FieldRead(assigned, owner, field) =>
      pps.add(s"FIELD-RD $assigned := $owner.$field")
    case InvokeFunc(assigned, receiver, func, typeArgs, args) =>
      pps.add(s"INVK-MTH $assigned := $receiver.$func")
      printTypeArgsList(typeArgs)
      printArgsList(args)
    case InvokeClosure(assigned, callee, args) =>
      pps.add(s"INVK-CLOS $assigned := $callee")
    case Instantiate(assigned, classOrRecordName, typeArgs) =>
      pps.add(s"INSTANTIATE $assigned := new $classOrRecordName")
      printTypeArgsList(typeArgs)
    case MkClosure(assigned, params, body) =>
      pps.add(s"MK-CLOS $assigned := (").add(mkFunctionParamsDescr(params)).add(")").indent {
        pps.add("body: ")
        printScope(body)
      }
    case TypeTest(assigned, testedValue, testedTypeId) =>
      pps.add(s"TYPE-TEST $assigned := $testedValue is $testedTypeId")
    case Conversion(assigned, inValue, targetType) =>
      pps.add(s"CONVERT $assigned := $inValue as $targetType")
    case SSA.FieldWrite(owner, field, rhs) =>
      pps.add(s"FIELD-WR $owner.$field := $rhs")
    case SSA.Return(retVal) =>
      pps.add(s"RET $retVal")
    case SSA.Panic(msg) =>
      pps.add(s"PANIC $msg")
    case SSA.Cast(inValue, target) =>
      pps.add(s"CAST $inValue as $target")
    case SSA.Drop(droppedValue) =>
      pps.add(s"DROP $droppedValue")
    case SSA.LocalDecl(localId, tpe) =>
      pps.add(s"DECL-LOCAL $localId : $tpe")
    case scope: Scope => printScope(scope)
  }

  private def printTypeArgsList(typeArgs: List[Type])(using pps: PrettyPrintString): Unit = {
    pps.add("[")
    traverseIterable(typeArgs.iterator) { tArg =>
      pps.add(tArg)
    } {
      pps.add(",")
    }
    pps.add("]")
  }

  private def printArgsList(args: List[IdValue])(using pps: PrettyPrintString): Unit = {
    pps.add("(")
    traverseIterable(args.iterator) { arg =>
      pps.add(arg)
    } {
      pps.add(",")
    }
    pps.add(")")
  }

  private def printVarData(variables: Iterable[VarData])(using pps: PrettyPrintString): Unit = {
    pps.add("variables: ").indent {
      traverseIterable(variables.iterator) { varData =>
        pps.add(varData.toString)
      } {
        pps.newLine()
      }
    }
  }

  private def mkTypeParamsDescr(typeParams: Iterable[TypeParamInfo]): String =
    if typeParams.isEmpty then "" else typeParams.mkString("[", ",", "]")

  private def mkTypeAliasParamsDescr(params: Iterable[(FunOrVarId, (Types.Type, Formulas.IdValue))]): String =
    if params.isEmpty then "" else params.map {
      case (paramId, (paramType, paramVal)) =>
        s"$paramVal: $paramType"
    }.mkString("(", ", ", ")")

  private def mkFunctionParamsDescr(params: Iterable[(NamedIdValue, Type)]): String =
    if params.isEmpty then "()" else params.map { (idVal, tpe) =>
      s"$idVal: $tpe"
    }.mkString("(", ", ", ")")

  private def mkSuperTypesDescr(supertypes: List[NamedType]): String =
    if supertypes.isEmpty then "" else s" extends ${supertypes.mkString(", ")}"

  private def mkPosDescr(posOpt: Option[Position]): String = posOpt match {
    case Some(pos) => s" at $pos"
    case None => ""
  }

  private def traverseIterable[T](iter: Iterator[T])(iterableDisplay: T => Unit)(step: => Unit): Unit = {
    while (iter.hasNext) {
      iterableDisplay(iter.next())
      if (iter.hasNext) {
        val _ = step
      }
    }
  }

  private def indent(str: String): String =
    str.lines()
      .map(indentUnit + _)
      .collect(Collectors.joining())

}
