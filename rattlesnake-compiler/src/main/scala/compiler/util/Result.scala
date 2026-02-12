package compiler.util

enum Result[T] {
  case Success(value: T)
  case Failure(errorMsg: String)
}
