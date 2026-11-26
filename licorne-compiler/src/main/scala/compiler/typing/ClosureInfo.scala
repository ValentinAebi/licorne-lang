package compiler.typing

import compiler.irs.ircorne.Formulas.NamedIdValue
import compiler.irs.ircorne.IRcorne.Scope
import compiler.lang.ExecutionEnvironment
import compiler.lang.Types.{Type, TypeVariable}
import compiler.pipeline.CompilationStep
import compiler.reporting.{Errors, Position}
import compiler.typing.contexts.TypeParamsContext
import compiler.valproxies.BranchingInfo

import scala.collection.mutable

final case class ClosureInfo(
                              params: List[(NamedIdValue, Type)],
                              body: Scope,
                              retTypeVar: TypeVariable,
                              branchingInfo: BranchingInfo,
                              requiredPureFromDefSite: Boolean,
                              typeParamsCtx: TypeParamsContext
                            ) extends ExecutionEnvironment {
  private val impurities = mutable.ListBuffer.empty[(String, Option[Position])]

  override def expectedResultType: Type = retTypeVar

  override def reportImpurity(msg: String, posOpt: Option[Position], er: Errors.ErrorReporter)(using CompilationStep): Unit = {
    if (requiredPureFromDefSite) {
      er.reportError(msg, posOpt)
    } else {
      impurities.addOne(msg, posOpt)
    }
  }

  def getImpurities: Iterable[(String, Option[Position])] = impurities

}
