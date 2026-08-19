package compiler.pipeline

enum CompilationStep {
  case Lexing
  case Parsing
  case SSAGeneration
  case ImportsAnalysis
  case MonotonicityAnalysis
  case TypeCandidatesInference
  case TypeAliasesAnalysis
  case SubtypingAnalysis
  case DeclarationsAnalysis
  case TypeChecking
  case OverridesAnalysis
  case CodeGen
  case StringWriting
}
