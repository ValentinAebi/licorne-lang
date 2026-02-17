package compiler.pipeline

enum CompilationStep {
  case Lexing
  case Parsing
  case SSAGeneration
  case TypeAliasesAnalysis
  case DeclarationsAnalysis
  case Typing1
  case Typing2
  case TypeChecking
  case StringWriting
}
