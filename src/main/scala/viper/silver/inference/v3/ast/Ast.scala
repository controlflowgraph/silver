package viper.silver.inference.v3.ast

import viper.silver.ast.Type

trait TermSub {
  def apply(t: Term): Term
}

case class MapTermSub(replacements: Map[Term, Term]) extends TermSub {
  def apply(t: Term): Term = {
    this.replacements.getOrElse(t, t)
  }
}

case class PredDef(name: String, body: LogicTerm) {

}

case class PredInst(name: String, args: Seq[Term]) {
  def pretty(): String = {
    s"${this.name}(${this.args.map(a => a.pretty()).mkString(", ")})"
  }

}

trait Term {
  def substitute(ts: TermSub): Term

  def pretty(): String
}

case class NullTerm() extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    "null"
  }
}

case class IntTerm(value: BigInt) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    s"${this.value}"
  }
}

case class PermFracTerm(a: Term, b: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(PermFracTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()}/${this.b.pretty()}"
  }
}

case class AddTerm(a: Term, b: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(PermFracTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} + ${this.b.pretty()}"
  }
}

case class SubTerm(a: Term, b: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(PermFracTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} - ${this.b.pretty()}"
  }
}

case class VarTerm(name: String, typ: Type) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    s"${this.name}"
  }
}

case class FieldAccTerm(src: Term, field: String, typ: Type) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(FieldAccTerm(
      this.src.substitute(ts),
      this.field,
      this.typ
    ))
  }

  def pretty(): String = {
    s"${this.src.pretty()}.${this.field}"
  }
}

trait LogicTerm extends Term {

}

case class BoolTerm(value: Boolean) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    s"${this.value}"
  }
}

case class AndTerm(a: LogicTerm, b: LogicTerm) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(AndTerm(
      this.a.substitute(ts).asInstanceOf[LogicTerm],
      this.b.substitute(ts).asInstanceOf[LogicTerm]
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} && ${this.b.pretty()}"
  }
}

case class OrTerm(a: LogicTerm, b: LogicTerm) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(OrTerm(
      this.a.substitute(ts).asInstanceOf[LogicTerm],
      this.b.substitute(ts).asInstanceOf[LogicTerm]
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} || ${this.b.pretty()}"
  }
}

case class NotTerm(t: LogicTerm) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(NotTerm(
      this.t.substitute(ts).asInstanceOf[LogicTerm]
    ))
  }

  def pretty(): String = {
    s"!${this.t.pretty()}"
  }
}

case class ImplTerm(prem: LogicTerm, cons: LogicTerm) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(ImplTerm(
      this.prem.substitute(ts).asInstanceOf[LogicTerm],
      this.cons.substitute(ts).asInstanceOf[LogicTerm]
    ))
  }

  def pretty(): String = {
    s"${this.prem.pretty()} ==> ${this.cons.pretty()}"
  }
}

case class EqCmpTerm(a: Term, b: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(EqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} == ${this.b.pretty()}"
  }
}

case class NotEqCmpTerm(a: Term, b: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(NotEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} != ${this.b.pretty()}"
  }
}

case class LessCmpTerm(a: Term, b: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(LessCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} <  ${this.b.pretty()}"
  }
}

case class LessEqCmpTerm(a: Term, b: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(LessEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} <= ${this.b.pretty()}"
  }
}

case class GreaterCmpTerm(a: Term, b: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(GreaterCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} >  ${this.b.pretty()}"
  }
}

case class GreaterEqCmpTerm(a: Term, b: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(GreaterEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} >= ${this.b.pretty()}"
  }
}

object PermAmount {
  val WRITE: PermFracTerm = PermFracTerm(IntTerm(1), IntTerm(1))
  val READ: PermFracTerm = PermFracTerm(IntTerm(1), IntTerm(2))
  val NONE: PermFracTerm = PermFracTerm(IntTerm(0), IntTerm(1))
}

case class PredInstAccTerm(pred: PredInst, perm: PermFracTerm) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(PredInstAccTerm(
      this.pred,
      this.perm.substitute(ts).asInstanceOf[PermFracTerm]
    ))
  }

  def pretty(): String = {
    s"acc(${this.pred.pretty()}, ${this.perm.pretty()})"
  }
}

case class PredFieldAccTerm(pred: FieldAccTerm, perm: PermFracTerm) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(PredFieldAccTerm(
      this.pred,
      this.perm.substitute(ts).asInstanceOf[PermFracTerm]
    ))
  }

  def pretty(): String = {
    s"acc(${this.pred.pretty()}, ${this.perm.pretty()})"
  }
}