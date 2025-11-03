package lang

enum ReassigStatus(val kw: Keyword) {
  case Val extends ReassigStatus(Keyword.Val)
  case Var extends ReassigStatus(Keyword.Var)
}
