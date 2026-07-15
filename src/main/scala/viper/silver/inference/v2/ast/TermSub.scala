package viper.silver.inference.v2.ast

case class TermSub(mapping: Map[Term, Term]) {
  def apply(e: Term): Term = {
    this.mapping.getOrElse(e, e)
  }
}
