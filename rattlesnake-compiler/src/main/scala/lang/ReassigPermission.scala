package lang

enum ReassigPermission(val kw: Keyword) {
  case Val extends ReassigPermission(Keyword.Val)
  case Var extends ReassigPermission(Keyword.Var)
}
