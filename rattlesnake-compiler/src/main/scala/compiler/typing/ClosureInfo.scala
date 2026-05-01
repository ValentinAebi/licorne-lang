package compiler.typing

import compiler.irs.ssa.SSA.Scope
import compiler.irs.ssa.Formulas.ParamIdValue
import compiler.lang.{ExecutionEnvironment, FunctionSignature}
import compiler.lang.Types.{Type, TypeVariable}
import compiler.typing.contexts.TypeParamsContext
import compiler.valproxies.BranchingInfo

final case class ClosureInfo(
                              params: List[(ParamIdValue, Type)],
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
