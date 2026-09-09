package viper.silver.inference.v3.knowledge

import viper.silver.inference.v3.ast.{ImplTerm, LogicTerm, TermSub}

case class Potential(partial: Set[ImplTerm]) {

  def this() = {
    this(Set())
  }

  def substitute(ts: TermSub): Potential = {
    Potential(this.partial.map(i => ImplTerm(
      i.prem.substitute(ts).asInstanceOf[LogicTerm],
      i.cons.substitute(ts).asInstanceOf[LogicTerm]
    )))
  }

  def pretty(): String = {
    this.partial.map(i => i.pretty()).toSeq.mkString("\n")
  }

  def inhale(partial: Seq[ImplTerm]): Potential = {
    // TODO: this merge can lose information when having two implications of the same form
    //       e.g. a ==> acc(A, 1/2) && b ==> a ==> acc(A, 1/2)
    //       with inhale b this would lead to merging
    //       a ==> acc(A, 1/2) && a ==> acc(A, 1/2)
    //      into just:   { a ==> acc(A, 1/2) }
    Potential(this.partial.union(partial.toSet))
  }
}