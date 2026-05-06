package compiler.util

import scala.reflect.ClassTag

extension [S, R](subject: S) def whenInstanceOf[T : ClassTag](f: T => R): Option[R] = subject match {
  case subject: T => Some(f(subject))
  case _ => None
}
