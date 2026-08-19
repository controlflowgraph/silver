package viper.silver.inference.v3.ast

import viper.silver.ast.Type
import viper.silver.inference.v3.FixedPoint

trait TermSub {
  def apply(t: Term): Term
}

case class MapTermSub(replacements: Map[Term, Term]) extends TermSub {
  def apply(t: Term): Term = {
    this.replacements.getOrElse(t, t)
  }
}

case class FuncTermSub(f: Term => Term) extends TermSub {
  def apply(t: Term): Term = {
    this.f(t)
  }
}

case class PredDef(name: String, params: Seq[String], body: LogicTerm) {
  def pretty(): String = {
    s"${this.name}(${this.params.mkString(", ")}) := ${this.body.pretty()})"
  }

  def instantiate(pred: PredInst) : LogicTerm = {
    val mapping = this.params.zip(pred.args).toMap
    val ts = FuncTermSub {
      case t@VarTerm(n, _) => mapping.getOrElse(n, t)
      case c => c
    }
    this.body.substitute(ts).asInstanceOf[LogicTerm]
  }
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

case class NegTerm(t: Term) extends Term {

  override def substitute(ts: TermSub): Term = {
    ts.apply(NegTerm(this.t.substitute(ts)))
  }

  override def pretty(): String = s"-${this.t.pretty()}"
}

case class AddTerm(a: Term, b: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(AddTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} + ${this.b.pretty()}"
  }
}

case class MulTerm(a: Term, b: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(MulTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.a.pretty()} * ${this.b.pretty()}"
  }
}

case class SubTerm(a: Term, b: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(SubTerm(
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

trait Comparison {
  def negate(): Comparison

  def pretty(): String

  def subst(ts: TermSub): Comparison
}

case class EqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(EqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison ={
    EqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }

  def pretty(): String = {
    s"${this.a.pretty()} == ${this.b.pretty()}"
  }

  override def negate(): Comparison = NotEqCmpTerm(this.a, this.b)
}

case class NotEqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(NotEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison ={
    NotEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} != ${this.b.pretty()}"
  }

  override def negate(): Comparison = EqCmpTerm(this.a, this.b)
}

case class LessCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(LessCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison ={
    LessCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} <  ${this.b.pretty()}"
  }

  override def negate(): Comparison = GreaterEqCmpTerm(this.a, this.b)
}

case class LessEqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(LessEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }


  def subst(ts: TermSub): Comparison ={
    LessEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} <= ${this.b.pretty()}"
  }

  override def negate(): Comparison = GreaterCmpTerm(this.a, this.b)
}

case class GreaterCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(GreaterCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison ={
    GreaterCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} >  ${this.b.pretty()}"
  }

  override def negate(): Comparison = LessEqCmpTerm(this.a, this.b)
}

case class GreaterEqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(GreaterEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison ={
    GreaterEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} >= ${this.b.pretty()}"
  }

  override def negate(): Comparison = LessCmpTerm(this.a, this.b)
}

object PermAmount {
  val WRITE: PermFracTerm = PermFracTerm(IntTerm(1), IntTerm(1))
  val READ: PermFracTerm = PermFracTerm(IntTerm(1), IntTerm(2))
  val NONE: PermFracTerm = PermFracTerm(IntTerm(0), IntTerm(1))
}

case class PredInstAccTerm(pred: PredInst, perm: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(PredInstAccTerm(
      PredInst(
        this.pred.name,
        this.pred.args.map(a => a.substitute(ts))
      ),
      this.perm.substitute(ts)
    ))
  }

  def scale(f: Term): PredInstAccTerm = {
    PredInstAccTerm(this.pred, MulTerm(this.perm, f))
  }

  def pretty(): String = {
    s"acc(${this.pred.pretty()}, ${this.perm.pretty()})"
  }
}

case class PredFieldAccTerm(exp: FieldAccTerm, perm: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(PredFieldAccTerm(
      this.exp.substitute(ts).asInstanceOf[FieldAccTerm],
      this.perm.substitute(ts)
    ))
  }

  def scale(f: Term): PredFieldAccTerm = {
    PredFieldAccTerm(this.exp, MulTerm(this.perm, f))
  }

  def pretty(): String = {
    s"acc(${this.exp.pretty()}, ${this.perm.pretty()})"
  }
}

object TermRewriter
{
  private def constSubSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case SubTerm(a, b) => AddTerm(a, NegTerm(b))
      case c => c
    }
  )

  private def constNegSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case NegTerm(PermFracTerm(IntTerm(q), b)) => PermFracTerm(IntTerm(-q), b)
      case c => c
    },
    FuncTermSub {
      case NegTerm(NegTerm(a)) => a
      case c => c
    }
  )

  private def constAddSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case AddTerm(PermFracTerm(IntTerm(a), IntTerm(b)), PermFracTerm(IntTerm(c), IntTerm(d))) => PermFracTerm(
        IntTerm(a * d + c * b),
        IntTerm(b * d)
      )
      case c => c
    }
  )

  private def constMulSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case MulTerm(PermFracTerm(IntTerm(a), IntTerm(b)), PermFracTerm(IntTerm(c), IntTerm(d))) => PermFracTerm(
        IntTerm(a * c),
        IntTerm(b * d)
      )
      case c => c
    }
  )


  private def normalizeConstAdd: Seq[TermSub] = Seq(
    FuncTermSub {
      case t@AddTerm(_: PermFracTerm, _: PermFracTerm) => t
      case AddTerm(a: PermFracTerm, b) => AddTerm(b, a)
      case c => c
    }
  )

  private def normalizeAddTermOrder: Seq[TermSub] = Seq(
    FuncTermSub {
      case AddTerm(AddTerm(a, b), c) => AddTerm(a, AddTerm(b, c))
      case c => c
    }
  )

  private def rewriteConstantAdds: Seq[TermSub] = Seq(
    FuncTermSub {
      case t@AddTerm(_: PermFracTerm, AddTerm(_: PermFracTerm, _)) => t
      case AddTerm(a: PermFracTerm, AddTerm(b, c)) => AddTerm(b, AddTerm(a, c))
      case c => c
    }
  )

  def simplify(t: Term): Term = {

    val subs = Seq(
      constAddSimp,
      constMulSimp,
      constSubSimp,
      constNegSimp,
      normalizeConstAdd,
      normalizeAddTermOrder,
      rewriteConstantAdds
    ).flatten
    val func = FuncTermSub(f => {
      subs.foldLeft(f)((v, q) => v.substitute(q))
    })
    FixedPoint.compute(t, (p: Term) => p.substitute(func))
  }
}