package compiler.lang

import compiler.identifiers.FunOrVarId
import compiler.irs.SSA.{FieldResolutionTarget, InvocationTarget, Scope}
import compiler.util.SeqSet

// TODO cleaner pretty-printing system
object Formulas {

  sealed trait Formula

  sealed trait IdValue extends Formula {
    def uid: Long

    def definingScope: Scope
  }

  sealed trait NamedIdValue(valKindDescr: String) extends IdValue {
    def name: String

    override def toString: String =
      s"$name#$uid@${definingScope.scopeUid}$valKindDescr"
  }

  final case class ParamIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue("p") {
    override def name: String = id.stringId
  }

  final case class ValIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue("s") {
    override def name: String = id.stringId
  }

  final case class VarIdValue(id: FunOrVarId, definingScope: Scope, uid: Long) extends NamedIdValue("r") {
    override def name: String = id.stringId
  }

  final case class UninterpretedConstIdValue(name: String, definingScope: Scope, uid: Long) extends NamedIdValue("c")

  final case class IntermediateIdValue(definingScope: Scope, uid: Long, nameHintOpt: Option[String]) extends IdValue {
    override def toString: String = s"${"$"}$uid@${definingScope.scopeUid}i"
  }

  sealed trait ConstFormula extends Formula {
    def value: Any

    override def toString: String = value.toString
  }

  final case class IntConst(value: Int) extends ConstFormula

  final case class BoolConst(value: Boolean) extends ConstFormula

  final case class StringConst(value: String) extends ConstFormula

  final case class Select(owner: Formula, var field: FieldResolutionTarget) extends Formula {
    override def toString: String = s"$owner.$field"
  }
  
  final case class Call(receiver: Formula, var func: InvocationTarget, args: List[Formula]) extends Formula {
    override def toString: String =
      s"$receiver.$func" ++ args.mkString("(", ",", ")")
  }

  final case class Plus(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = lhs.toString
      val opAndRhsStr = rhs match {
        case Neg(negated) => s" - $negated"
        case rhs => s" + $rhs"
      }
      lhsStr ++ opAndRhsStr
    }
  }

  final case class Neg(operand: Formula) extends Formula {
    override def toString: String = "-" + parenthIfNot[IdValue | ConstFormula](operand)
  }

  final case class Times(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr * $rhsStr"
    }
  }

  final case class DivBy(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr / $rhsStr"
    }
  }

  final case class Modulo(lhs: Formula, rhs: Formula) extends Formula {
    override def toString: String = {
      val lhsStr = parenthIf[Plus | Neg](lhs)
      val rhsStr = parenthIfNot[IdValue | ConstFormula](rhs)
      s"$lhsStr % $rhsStr"
    }
  }

  private inline def parenthIf[F <: Formula](inline term: Formula): String = {
    val parenth = term.isInstanceOf[F]
    if parenth then s"($term)" else term.toString
  }

  private inline def parenthIfNot[F <: Formula](inline term: Formula): String = {
    val parenth = !term.isInstanceOf[F]
    if parenth then s"($term)" else term.toString
  }

  // TODO may be optimized: when operand(s) do not change, return input as is
  extension (formula: Formula) def substitute(subst: Map[IdValue, Formula]): Formula = formula match {
    case value: IdValue => subst.getOrElse(value, value)
    case c: IntConst => c
    case c: BoolConst => c
    case c: StringConst => c
    case Select(owner, field) => Select(owner.substitute(subst), field)
    case Call(receiver, funId, args) => Call(receiver.substitute(subst), funId, args.map(_.substitute(subst)))
    case Plus(lhs, rhs) => Plus(lhs.substitute(subst), rhs.substitute(subst))
    case Neg(operand) => Neg(operand.substitute(subst))
    case Times(lhs, rhs) => Times(lhs.substitute(subst), rhs.substitute(subst))
    case DivBy(lhs, rhs) => DivBy(lhs.substitute(subst), rhs.substitute(subst))
    case Modulo(lhs, rhs) => Modulo(lhs.substitute(subst), rhs.substitute(subst))
  }
  
  extension (formula: Formula) def simplified: Formula = {
    var summaryOpt = Option.empty[Formula]

    def addToSummary(f: Formula): Unit = {
      summaryOpt = Some(summaryOpt match {
        case Some(summary) => Plus(summary, f)
        case None => f
      })
    }

    var cstOpt = Option.empty[Int]
    for ((f, coef) <- linearize(formula)) {
      f match {
        case IntConst(1) =>
          assert(cstOpt.isEmpty)
          cstOpt = Some(coef)
        case _ if coef == 0 => ()
        case _ if coef == 1 =>
          addToSummary(f)
        case _ if coef == -1 =>
          addToSummary(Neg(f))
        case _ =>
          addToSummary(Times(IntConst(coef), f))
      }
    }
    cstOpt.foreach { cst =>
      addToSummary(IntConst(cst))
    }
    summaryOpt.getOrElse(IntConst(0))
  }
  
  private def linearize(formula: Formula): Map[Formula, Int] = formula match {
    case value: IdValue => Map(value -> 1)
    case IntConst(cst) => Map(IntConst(1) -> cst)
    case formula: ConstFormula => Map(formula -> 1)
    case Select(owner, field) => Map(formula -> 1)
    case Call(receiver, func, args) => Map(formula -> 1)
    case Plus(lhs, rhs) =>
      val lLin = linearize(lhs)
      val rLin = linearize(rhs)
      Map.from(for (f <- lLin.keys ++ rLin.keys) yield {
        val coef = lLin.getOrElse(f, 0) + rLin.getOrElse(f, 0)
        f -> coef
      })
    case Neg(operand) =>
      for ((f, coef) <- linearize(operand)) yield (f, -coef)
    case Times(lhs, rhs) =>
      Map(formula -> 1)
    case DivBy(lhs, rhs) =>
      Map(formula -> 1)
    case Modulo(lhs, rhs) =>
      Map(formula -> 1)
  }

}
