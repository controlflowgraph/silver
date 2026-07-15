package viper.silver.inference.v2.ast

trait Line {
  def pretty(): String = this.pretty(0)
  def pretty(indent: Int): String

}

case class VarAssignLine(v: Var, e: Term) extends Line {
  def pretty(indent: Int): String = {
    (" " * indent) + this.v.pretty() + " := " + e.pretty()
  }
}

case class FieldAssignLine(v: FieldAcc, e: Term) extends Line {
  def pretty(indent: Int): String = {
    (" " * indent) + this.v.pretty() + " := " + e.pretty()
  }
}
//
//case class MethodCallLine(vs: Seq[Var], method: String, args: Seq[Term]) extends Line {
//
//}

case class InhaleLine(pred: PredTerm) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}inhale: ${pred.pretty()}"
  }
}

case class ExhaleLine(pred: PredTerm) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}exhale: ${this.pred.pretty()}"
  }
}

case class AssumeLine(pred: PredTerm) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}assume: ${pred.pretty()}"
  }
}

case class AssertLine(pred: PredTerm) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}assert: ${pred.pretty()}"
  }
}

case class NonDetBranch(first: Line, second: Line) extends Line {
  def pretty(indent: Int): String = {
    s"${" " * indent}{\n${this.first.pretty(indent + 4)}\n${" " * indent}} [] {\n${this.second.pretty(indent + 4)}${" " * indent}}"
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