package viper.silver.inference.v2.ast

import viper.silver.ast.{Exp, Injection, Stmt}
import viper.silver.inference.v2.knowledge.Knowledge

trait Line {

  def pretty(): String = this.pretty(0)

  def pretty(indent: Int): String

}

case class VarAssignLine(location: Injection, v: Var, e: Term) extends Line {
  def pretty(indent: Int): String = {
    (" " * indent) + this.v.pretty() + " := " + e.pretty()
  }
}

case class FieldAssignLine(location: Injection, v: FieldAcc, e: Term) extends Line {
  def pretty(indent: Int): String = {
    (" " * indent) + this.v.pretty() + " := " + e.pretty()
  }
}

case class InhaleLine(pred: PredTerm) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}inhale: ${pred.pretty()}"
  }
}

case class ExhaleLine(location: Injection, pred: PredTerm) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}exhale: ${this.pred.pretty()}"
  }
}

case class AssumeLine(pred: PredTerm, knowledge: Set[Knowledge]) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}assume: PRED: ${pred.pretty()} && KM: ${this.knowledge.map(_.pretty()).mkString(" & ")}"
  }
}

case class AssertLine(location: Injection, pred: PredTerm) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}assert: ${pred.pretty()}"
  }
}

case class Branching(location: Injection, cond: Exp, first: Line, second: Line, firstInj: Injection, secondInj: Injection) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}${cond}\n${" " * indent}{\n${this.first.pretty(indent + 4)}\n${" " * indent}} [] {\n${this.second.pretty(indent + 4)}\n${" " * indent}}"
  }
}

case class Sequence(lines: Seq[Line]) extends Line {
  def prepend(line: Line) : Sequence = {
    prepend(Seq(line))
  }

  def prepend(lines: Seq[Line]) : Sequence = {
    Sequence(lines ++ this.lines)
  }

  def append(line: Line) : Sequence = {
    append(Seq(line))
  }

  def append(lines: Seq[Line]) : Sequence = {
    Sequence(lines ++ this.lines)
  }

  def join(other: Sequence) : Sequence = {
    Sequence(this.lines ++ other.lines)
  }

  def pretty(indent: Int): String = this.lines.map(_.pretty(indent)).mkString("\n")
}