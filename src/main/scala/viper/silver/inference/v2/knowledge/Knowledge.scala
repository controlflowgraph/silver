package viper.silver.inference.v2.knowledge

import viper.silver.inference.v2.ast.{PredTerm, Term, TermSub}

trait Knowledge {

  def substitute(ts: TermSub): Knowledge

  def pretty() : String
}

case class IsNull(e: Term) extends Knowledge {

  def substitute(ts: TermSub): Knowledge = {
    IsNull(this.e.substitute(ts))
  }

  def pretty() : String= {
    this.e.pretty() + " == null"
  }
}

case class IsNonNull(e: Term) extends Knowledge {

  def substitute(ts: TermSub): Knowledge = {
    IsNonNull(this.e.substitute(ts))
  }

  def pretty() : String= {
    this.e.pretty() + " != null"
  }
}

case class Equivalence(a: Term, b: Term) {

}

