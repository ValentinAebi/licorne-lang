package compiler.smt

import compiler.irs.ssa.Formulas.IdValue
import io.ksmt.expr.KExpr
import io.ksmt.solver.KModel

import java.util.StringJoiner
import scala.collection.mutable


final class CounterexampleBox {
  private var model = Option.empty[KModel]
  private val tracked = mutable.LinkedHashMap.empty[KExpr[?], IdValue]

  def reinitialize(): Unit = {
    model = None
    tracked.clear()
  }

  def track(idVal: IdValue, kExpr: KExpr[?]): Unit = {
    tracked.put(kExpr, idVal)
  }

  def setModel(model: KModel): Unit = {
    this.model = Some(model)
  }

  def describe: Option[String] = model.map { model =>
    val sj = StringJoiner(", ")
    for ((kExpr, idVal) <- tracked) {
      try {
        val value = model.eval(kExpr, false)
        sj.add(s"$idVal == $value")
      } catch {
        case e: Exception => ()
      }
    }
    sj.toString
  }

}
