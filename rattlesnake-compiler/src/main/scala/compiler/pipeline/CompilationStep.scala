package compiler.pipeline

enum CompilationStep {
  case Lexing
  case Parsing
  case SSAGeneration
  case TypeAliasesAnalysis
  case SubtypingAnalysis
  case DeclarationsAnalysis
  case TypeChecking
  case StringWriting
}
