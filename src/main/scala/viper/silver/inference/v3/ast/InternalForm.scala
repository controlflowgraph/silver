package viper.silver.inference.v3.ast

import viper.silver.ast.{Injection, Type}
import viper.silver.inference.v3.Counter

import scala.collection.mutable

case class Ident(value: Int) {
  def pretty(): String = {
    s"${this.value}"
  }
}

trait Line {
  def ln: Ident

  def pretty(): String
}

case class LocalAssignLine(ln: Ident, inj: Injection, variable: VarTerm, value: Term) extends Line {
  def pretty(): String = {
    s"${this.ln.pretty()} [${this.inj.id}] ${this.variable.pretty()} := ${this.value.pretty()}"
  }
}

case class FieldAssignLine(ln: Ident, inj: Injection, fa: FieldAccTerm, value: Term) extends Line {
  def pretty(): String = {
    s"${this.ln.pretty()} [${inj.id}] ${this.fa.pretty()} := ${this.value.pretty()}"
  }
}

case class AssumeLine(ln: Ident, exp: LogicTerm) extends Line {
  def pretty(): String = {
    s"${this.ln.pretty()} assume ${this.exp.pretty()}"
  }
}

case class AssertLine(ln: Ident, inj: Injection, exp: LogicTerm) extends Line {
  def pretty(): String = {
    s"${this.ln.pretty()} [${this.inj}] assert ${this.exp.pretty()}"
  }
}

case class InhaleLine(ln: Ident, exp: LogicTerm) extends Line {

  def pretty(): String = {
    s"${this.ln.pretty()} inhale ${this.exp.pretty()}"
  }
}

case class ExhaleLine(ln: Ident, inj: Injection, exp: LogicTerm) extends Line {
  def pretty(): String = {
    s"${this.ln.pretty()} [${this.inj.id}] exhale ${this.exp.pretty()}"
  }
}

case class BranchLine(ln: Ident, pre: Injection, cond: LogicTerm, thn: Ident, els: Ident) extends Line {
  def pretty(): String = {
    s"${this.ln.pretty()} [${this.pre.id}] branch ${this.cond.pretty()}    [ ${this.thn.pretty()} ; ${this.els.pretty()} ]"
  }
}

case class CallLine(ln: Ident, inj: Injection, method: String, targets: Seq[VarTerm], args: Seq[Term]) extends Line {
  def pretty(): String = {
    s"${this.ln.pretty()} [${this.inj.id}] call ${this.method} (${this.args.map(a => a.pretty()).mkString(", ")})"
  }
}

case class InternalMethod(method: String, args: Seq[(String, Type)], pres: Seq[LogicTerm], posts: Seq[LogicTerm], start: Ident, stop: Set[Ident], rep: InternalRepresentation) {

}

case class InternalRepresentation(counter: Counter, lines: mutable.HashMap[Ident, Line], mesh: mutable.HashMap[Ident, mutable.HashSet[Ident]]) {
  def this() = {
    this(Counter(0), new mutable.HashMap(), new mutable.HashMap())
  }

  def introduce(prev: Set[Ident], line: Line): Unit = {
    addLine(line)
    addConnections(prev, line.ln)
  }

  def addLine(line: Line): Unit = {
    this.lines.put(line.ln, line)
    if (!this.mesh.contains(line.ln)) {
      this.mesh.put(line.ln, new mutable.HashSet())
    }
  }

  def addConnections(from: Set[Ident], to: Ident): Unit = {
    from.foreach(f => addConnection(f, to))
  }

  def addConnection(from: Ident, to: Ident): Unit = {
    if (!this.mesh.contains(from)) {
      this.mesh.put(from, new mutable.HashSet())
    }
    this.mesh(from).add(to)
  }

  def freshIdent() : Ident = {
    Ident(this.counter.next())
  }

  def pretty(): String = {
    val barrier = "%" * 100
    val linesPretty = this.lines.toSeq.sortBy(l => l._1.value)
      .map(e => "\t" + e._2.pretty()).mkString("\n")
    val meshPretty = this.mesh.toSeq.sortBy(e => e._1.value)
      .map(e => s"\t${e._1.pretty()}  ==>  ${e._2.map(_.pretty()).mkString(", ")}")
      .mkString("\n")
    s"${barrier}\ncurrent counter: ${counter.value}\nlines:\n${linesPretty}\nmesh:\n${meshPretty}\n${barrier}"
  }
}