package compiler.pipeline

enum CompilationStep {
  case Lexing
  case Parsing
  case SSAGeneration
  case MonotonicityAnalysis
  case TypeHintsInsertion
  case TypeAliasesAnalysis
  case SubtypingAnalysis
  case DeclarationsAnalysis
  case TypeChecking
  case StringWriting
}
