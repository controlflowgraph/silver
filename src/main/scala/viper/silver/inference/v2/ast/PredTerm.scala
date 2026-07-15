package viper.silver.inference.v2.ast

import viper.silver.inference.v2.PredInstance
import viper.silver.inference.v2.knowledge.Knowledge

trait PredTerm {
  def substitute(ts: TermSub): PredTerm
}

case class PredImpl(cond: Set[Knowledge], body: PredTerm) extends PredTerm {
  def substitute(ts: TermSub): PredImpl = {
    PredImpl(
      this.cond.map(c => c.substitute(ts)),
      this.body.substitute(ts)
    )
  }
}

case class PredTrue() extends PredTerm {

  def substitute(ts: TermSub): PredTrue = {
    PredTrue()
  }

}

case class PredAnd(a: PredTerm, b: PredTerm) extends PredTerm {
  def substitute(ts: TermSub): PredAnd = {
    PredAnd(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }
}

case class PredFieldAcc(fa: FieldAcc) extends PredTerm {
  def substitute(ts: TermSub): PredFieldAcc = {
    PredFieldAcc(
      this.fa.substitute(ts).asInstanceOf[FieldAcc]
    )
  }
}

case class PredPredAcc(pred: PredInstance) extends PredTerm {
  def substitute(ts: TermSub): PredPredAcc = {
    PredPredAcc(
      this.pred.substitute(ts)
    )
  }
}

case class PredNot(pred: PredTerm) extends PredTerm {
  def substitute(ts: TermSub): PredNot = {
    PredNot(
      this.pred.substitute(ts)
    )
  }
}