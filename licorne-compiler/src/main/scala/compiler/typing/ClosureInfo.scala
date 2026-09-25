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
                              containingEnvir: ExecutionEnvironment,
                              typeParamsCtx: TypeParamsContext
                            ) extends ExecutionEnvironment {

  override def expectedResultType: Type = retTypeVar

  override def root: FunctionSignature = containingEnvir.root
}
