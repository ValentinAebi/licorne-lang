package lang

enum Keyword(val str: String) {
  case As extends Keyword("as")
  case Cap extends Keyword("cap")
  case Class extends Keyword("class")
  case Const extends Keyword("const")
  case Datatype extends Keyword("datatype")
  case Else extends Keyword("else")
  case Fn extends Keyword("fn")
  case For extends Keyword("for")
  case Fs extends Keyword("fs")
  case If extends Keyword("if")
  case Interface extends Keyword("interface")
  case Is extends Keyword("is")
  case Main extends Keyword("main")
  case New extends Keyword("new")
  case Object extends Keyword("object")
  case Panic extends Keyword("panic")
  case Private extends Keyword("private")
  case Return extends Keyword("return")
  case Struct extends Keyword("struct")
  case Then extends Keyword("then")
  case This extends Keyword("this")
  case Typealias extends Keyword("typealias")
  case Val extends Keyword("val")
  case Var extends Keyword("var")
  case When extends Keyword("when")
  case With extends Keyword("with")
  case While extends Keyword("while")

  override def toString: String = str
}
