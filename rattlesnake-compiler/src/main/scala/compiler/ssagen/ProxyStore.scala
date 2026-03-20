package compiler.ssagen

import compiler.lang.Formulas.{Formula, IdValue}

import scala.collection.mutable


final class ProxyStore {
  private val proxies = mutable.Map.empty[IdValue, Formula]

  def saveProxy(idVal: IdValue, proxyOpt: Option[Formula]): Unit = proxyOpt.foreach { proxy =>
    saveProxy(idVal, proxy)
  }

  def saveProxy(idVal: IdValue, proxy: Formula): Unit = {
    if (proxies.contains(idVal)) {
      throw IllegalStateException(s"proxy already set for value $idVal")
    }
    proxies(idVal) = proxy
  }

  def getProxy(idVal: IdValue): Option[Formula] = proxies.get(idVal)

}
