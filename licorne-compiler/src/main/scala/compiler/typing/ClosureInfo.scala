package compiler.typing

import compiler.irs.ircorne.Formulas.NamedIdValue
import compiler.irs.ircorne.IRcorne.Scope
import compiler.lang.Types.{Type, TypeVariable}
import compiler.lang.{ExecutionEnvironment, FunctionSignature}
import compiler.typing.contexts.TypeParamsContext
import compiler.valproxies.BranchingInfo

final case class ClosureInfo(
                              params: List[(NamedIdValue, Type)],
                              body: Scope,
                              retTypeVar: TypeVariable,
                              branchingInfo: BranchingInfo,
                              requiresPurityInBody: Boolean,
                              typeParamsCtx: TypeParamsContext
                            ) extends ExecutionEnvironment {

  override def expectedResultType: Type = retTypeVar
}
