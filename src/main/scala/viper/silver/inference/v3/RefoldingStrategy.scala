package viper.silver.inference.v3

import viper.silver.inference.v3.ast._

trait RefoldingStep {
  def scale(f: Term): RefoldingStep

  def pretty(): String

  def rewrite(ts: TermSub): RefoldingStep
}

case class PackageStep(wand: BaguetteMagic, steps: Seq[RefoldingStep]) extends RefoldingStep {
  def scale(f: Term): RefoldingStep = {
    PackageStep(this.wand.scale(f), this.steps.map(s => s.scale(f)))
  }

  def pretty(): String = {
    s"package [${this.wand.pretty()}] {\n${this.steps.map(_.pretty()).mkString("\n").indent(2)}\n}"
  }

  def rewrite(ts: TermSub): RefoldingStep = {
    PackageStep(this.wand.rewrite(ts), this.steps.map(_.rewrite(ts)))
  }
}

case class UnfoldingStep(pred: PredInst, perm: Term, subs: Seq[RefoldingStep]) extends RefoldingStep {
  def scale(f: Term): RefoldingStep = {
    UnfoldingStep(this.pred, MulTerm(this.perm, f), this.subs.map(s => s.scale(f)))
  }

  def pretty(): String = {
    s"unfolding ${this.pred.pretty()} => ${this.perm.pretty()}\n${this.subs.map(_.pretty()).mkString("\n").indent(2)}"
  }

  def rewrite(ts: TermSub): RefoldingStep = {
    val up = PredInst(this.pred.name, this.pred.args.map(a => a.substitute(ts)))
    val perm = this.perm.substitute(ts)
    val subs = this.subs.map(_.rewrite(ts))
    UnfoldingStep(up, perm, subs)
  }
}

case class FoldingStep(pred: PredInst, perm: Term) extends RefoldingStep {
  def scale(f: Term): RefoldingStep = {
    FoldingStep(this.pred, MulTerm(this.perm, f))
  }

  def pretty(): String = {
    s"folding ${this.pred.pretty()}; ${this.perm.pretty()}"
  }

  def rewrite(ts: TermSub): RefoldingStep = {
    val up = PredInst(this.pred.name, this.pred.args.map(a => a.substitute(ts)))
    val perm = this.perm.substitute(ts)
    FoldingStep(up, perm)
  }
}

case class RefoldingStrategy(steps: Seq[RefoldingStep]) {
  def pretty(): String = {
    s"${this.steps.map(_.pretty()).mkString("\n")}"
  }

  def rewrite(ts: TermSub): RefoldingStrategy = {
    RefoldingStrategy(this.steps.map(s => s.rewrite(ts)))
  }
}