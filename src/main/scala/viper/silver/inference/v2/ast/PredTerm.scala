package viper.silver.inference.v2.ast

import viper.silver.inference.v2.PredInstance
import viper.silver.inference.v2.knowledge.Knowledge

trait PredTerm {
  def substitute(ts: TermSub): PredTerm

  def pretty(): String

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm]
}

case class PredImpl(cond: Set[Knowledge], body: PredTerm) extends PredTerm {
  def substitute(ts: TermSub): PredImpl = {
    PredImpl(
      this.cond.map(c => c.substitute(ts)),
      this.body.substitute(ts)
    )
  }

  override def pretty(): String = this.cond.map(_.pretty()).mkString(" & ") + " ==> " + this.body.pretty()

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    // TODO: replace knowledge with pred term
    f(this.body.rewrite(f).map(v => PredImpl(this.cond, v)).getOrElse(this))
  }
}

case class PredTrue() extends PredTerm {

  def substitute(ts: TermSub): PredTrue = {
    PredTrue()
  }

  override def pretty(): String = "True"

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    f(this)
  }
}

case class PredFalse() extends PredTerm {

  def substitute(ts: TermSub): PredFalse = {
    PredFalse()
  }

  override def pretty(): String = "False"

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    f(this)
  }
}


case class PredAnd(a: PredTerm, b: PredTerm) extends PredTerm {
  def substitute(ts: TermSub): PredAnd = {
    PredAnd(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }

  override def pretty(): String = this.a.pretty() + " && " + this.b.pretty()

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    (this.a.rewrite(f), this.b.rewrite(f)) match {
      case (None, None) => f(this)
      case (rA, rB) => f(PredAnd(
        rA.getOrElse(this.a),
        rB.getOrElse(this.b)
      ))
    }
  }
}

case class PredOr(a: PredTerm, b: PredTerm) extends PredTerm {
  def substitute(ts: TermSub): PredOr = {
    PredOr(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }

  override def pretty(): String = this.a.pretty() + " || " + this.b.pretty()

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    (this.a.rewrite(f), this.b.rewrite(f)) match {
      case (None, None) => f(this)
      case (rA, rB) => f(PredOr(
        rA.getOrElse(this.a),
        rB.getOrElse(this.b)
      ))
    }
  }
}

case class PredFieldAcc(fa: FieldAcc) extends PredTerm {
  def substitute(ts: TermSub): PredFieldAcc = {
    PredFieldAcc(
      this.fa.substitute(ts).asInstanceOf[FieldAcc]
    )
  }

  override def pretty(): String = "acc(" + this.fa.pretty() + ")"

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    f(this)
  }
}

case class PredPredAcc(pred: PredInstance) extends PredTerm {
  def substitute(ts: TermSub): PredPredAcc = {
    PredPredAcc(
      this.pred.substitute(ts)
    )
  }

  override def pretty(): String = "acc(" + this.pred.pretty() + ")"

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    f(this)
  }
}

case class PredNot(pred: PredTerm) extends PredTerm {
  def substitute(ts: TermSub): PredNot = {
    PredNot(
      this.pred.substitute(ts)
    )
  }

  override def pretty(): String = "!" + this.pred.pretty()

  def rewrite(f: PredTerm => Option[PredTerm]): Option[PredTerm] = {
    f(this.pred.rewrite(f).map(v => PredNot(v)).getOrElse(this))
  }
}


object PredRewriter {
  def rewrite(f: PredTerm => Option[PredTerm], t: PredTerm): PredTerm = {
    f(t).getOrElse(t)
  }

  def fix(f: PredTerm => PredTerm, t: PredTerm): PredTerm = {
    val applied = f(t)
    if (t.equals(applied)) {
      t
    }
    else {
      fix(f, applied)
    }
  }

  private val literalNegation: Seq[PredTerm => Option[PredTerm]] = Seq(
    (v: PredTerm) => v match {
      case PredNot(PredTrue()) => Some(PredFalse())
      case _ => None
    },
    (v: PredTerm) => v match {
      case PredNot(PredFalse()) => Some(PredTrue())
      case _ => None
    }
  )

  private val andSimplification: Seq[PredTerm => Option[PredTerm]] = Seq(
    (v: PredTerm) => v match {
      case PredAnd(PredTrue(), q) => Some(q)
      case _ => None
    },
    (v: PredTerm) => v match {
      case PredAnd(q, PredTrue()) => Some(q)
      case _ => None
    }
  )

  private val orSimplification: Seq[PredTerm => Option[PredTerm]] = Seq(
    (v: PredTerm) => v match {
      case PredOr(PredFalse(), q) => Some(q)
      case _ => None
    },
    (v: PredTerm) => v match {
      case PredOr(q, PredFalse()) => Some(q)
      case _ => None
    }
  )

  private val orShortCircuit: Seq[PredTerm => Option[PredTerm]] = Seq(
    (v: PredTerm) => v match {
      case PredOr(PredTrue(), _) => Some(PredTrue())
      case _ => None
    },
    (v: PredTerm) => v match {
      case PredOr(_, PredTrue()) => Some(PredTrue())
      case _ => None
    }
  )

  private val andShortCircuit: Seq[PredTerm => Option[PredTerm]] = Seq(
    (v: PredTerm) => v match {
      case PredAnd(PredFalse(), _) => Some(PredFalse())
      case _ => None
    },
    (v: PredTerm) => v match {
      case PredAnd(_, PredFalse()) => Some(PredFalse())
      case _ => None
    }
  )

  private val implicationSimplification: Seq[PredTerm => Option[PredTerm]] = Seq(
//    (v: PredTerm) => v match {
//      case PredImpl(PredFalse(), _) => Some(PredTrue())
//      case _ => None
//    },
//    (v: PredTerm) => v match {
//      case PredImpl(PredTrue(), q) => Some(q)
//      case _ => None
//    }
  )

  private val deMorgan: Seq[PredTerm => Option[PredTerm]] = Seq(
    (v: PredTerm) => v match {
      case PredNot(PredAnd(a, b)) => Some(PredOr(PredNot(a), PredNot(b)))
      case _ => None
    },
    (v: PredTerm) => v match {
      case PredNot(PredOr(a, b)) => Some(PredAnd(PredNot(a), PredNot(b)))
      case _ => None
    }
  )

  private val simpDoubleNeg: Seq[PredTerm => Option[PredTerm]] = Seq(
    (v: PredTerm) => v match {
      case PredNot(PredNot(a)) => Some(a)
      case _ => None
    }
  )

  def simplify(pt: PredTerm): PredTerm = {
    val rewrites: Seq[PredTerm => Option[PredTerm]] = Seq(
      literalNegation,
      andSimplification,
      orSimplification,
      andShortCircuit,
      orShortCircuit,
      implicationSimplification,
      deMorgan,
      simpDoubleNeg
    ).flatten

    val fs = ((arg: PredTerm) => rewrites.foldLeft(arg)((a, f) => rewrite(f, a)))

    fix(fs, pt)
  }
}