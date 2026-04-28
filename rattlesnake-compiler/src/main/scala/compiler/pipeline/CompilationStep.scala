package compiler.pipeline

enum CompilationStep {
  case Lexing
  case Parsing
  case SSAGeneration
  case ImportsAnalysis
  case MonotonicityAnalysis
  case TypeHintsInsertion
  case TypeAliasesAnalysis
  case SubtypingAnalysis
  case DeclarationsAnalysis
  case TypeChecking
  case OverridesAnalysis
  case StringWriting
}
