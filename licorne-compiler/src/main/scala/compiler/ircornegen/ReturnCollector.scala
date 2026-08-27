package compiler.ircornegen

import compiler.irs.ircorne.Formulas.Formula

trait ReturnCollector {
  
  def offerReturn(retValProxy: Formula): Unit
  
  def giveUp(): Unit
}

object ReturnCollector {

  val doNothingCollector: ReturnCollector = new ReturnCollector {
    override def offerReturn(retValProxy: Formula): Unit = ()

    override def giveUp(): Unit = ()
  }
  
  def freshUniqueCollector: UniqueReturnCollector = new UniqueReturnCollector()
  
  final class UniqueReturnCollector private[ReturnCollector]() extends ReturnCollector {
    private var retValOpt = Option.empty[Formula]
    private var givenUpFlag = false

    override def offerReturn(retValProxy: Formula): Unit = {
      retValOpt match {
        case Some(_) =>
          giveUp()
        case None =>
          retValOpt = Some(retValProxy)
      }
    }

    override def giveUp(): Unit = {
      givenUpFlag = true
    }
    
    def getUniqueRet: Option[Formula] =
      retValOpt.filter(_ => !givenUpFlag)
  }
  
}
