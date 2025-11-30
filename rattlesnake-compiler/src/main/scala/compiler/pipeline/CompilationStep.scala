package compiler.pipeline

enum CompilationStep {
  case Lexing
  case Parsing
  case SSAGeneration
  case TypeChecking
  case StringWriting
}
