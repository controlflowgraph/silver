package viper.silver.inference.v2.ast

import viper.silver.ast.{Field, Method}

trait Line {

}

case class VarAssignLine(v: Var, e: Term) extends Line {

}

case class FieldAssignLine(v: FieldAcc, e: Term) extends Line {

}

case class MethodCallLine(vs: Seq[Var], method: String, args: Seq[Term]) extends Line {

}

case class InhaleLine(pred: PredTerm) extends Line {

}

case class ExhaleLine(pred: PredTerm) extends Line {

}

case class AssumeLine(pred: PredTerm) extends Line {

}

case class AssertLine(pred: PredTerm) extends Line {

}

case class NonDetBranch(first: Line, second: Line) extends Line {

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
}