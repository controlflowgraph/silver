package viper.silver.inference.v3.ast

import org.apache.commons.io.filefilter.PrefixFileFilter
import viper.silver.ast.{Add, And, BoolLit, CondExp, CurrentPerm, EqCmp, Exp, Field, FieldAccess, FieldAccessPredicate, FractionalPerm, GeCmp, GtCmp, Implies, IntLit, IntPermMul, LeCmp, LocalVar, LtCmp, MagicWand, Minus, Mul, NeCmp, Not, NullLit, Old, Or, PermAdd, PermMinus, PermMul, PredicateAccess, PredicateAccessPredicate, Ref, Sub, Type}
import viper.silver.inference.v3.{FixedPoint, MagicWandManager, ValRef}
import viper.silver.inference.v3.knowledge.{Assignment, DirectPermissionMask, FoldedPermissionMask, Heap, KnowledgeBase, Obj, Potential}

trait TermSub {
  def apply(t: Term): Term

  def followedBy(other: TermSub): TermSub = {
    FuncTermSub(t => {
      t.substitute(this)
        .substitute(other)
    })
  }
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

  def instantiate(pred: PredInst): LogicTerm = {
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

  def toExp(): Exp
}

case class OldTerm(e: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(OldTerm(
      this.e.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"old(${this.e.pretty()})"
  }

  override def toExp(): Exp = {
    Old(this.e.toExp())()
  }
}

case class CondTerm(cond: LogicTerm, left: Term, right: Term) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(CondTerm(
      this.cond.substitute(ts).asInstanceOf[LogicTerm],
      this.left.substitute(ts),
      this.right.substitute(ts)
    ))
  }

  def pretty(): String = {
    s"${this.cond.pretty()} ? ${this.left.pretty()} : ${this.right.pretty()}"
  }

  def toExp(): Exp = {
    CondExp(this.cond.toExp(), this.left.toExp(), this.right.toExp())()
  }
}

case class NullTerm() extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    "null"
  }

  override def toExp(): Exp = NullLit()()
}

case class IntTerm(value: BigInt) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    s"${this.value}"
  }

  override def toExp(): Exp = IntLit(this.value)()
}

case class FieldPermAmountTerm(e: FieldAccTerm) extends Term {
  def substitute(ts: TermSub): Term = {
    ts.apply(FieldPermAmountTerm(
      this.e.substitute(ts).asInstanceOf[FieldAccTerm]))
  }

  def pretty(): String = {
    s"perm(${this.e.pretty()})"
  }

  override def toExp(): Exp = CurrentPerm(this.e.toExp())()
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

  override def toExp(): Exp = FractionalPerm(
    this.a.toExp(),
    this.b.toExp()
  )()
}

case class NegTerm(t: Term) extends Term {

  override def substitute(ts: TermSub): Term = {
    ts.apply(NegTerm(this.t.substitute(ts)))
  }

  override def pretty(): String = s"(-(${this.t.pretty()}))"

  override def toExp(): Exp = {
    val exp = this.t.toExp()
    if (exp.typ.equals(viper.silver.ast.Perm)) {
      PermMinus(exp)()
    }
    else {
      Minus(exp)()
    }
  }
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

  override def toExp(): Exp = {
    val leftExp = this.a.toExp()
    val rightExp = this.b.toExp()
    if (leftExp.typ == viper.silver.ast.Perm) {
      PermAdd(leftExp, rightExp)()
    }
    else {
      Add(leftExp, rightExp)()
    }
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

  override def toExp(): Exp = {
    val expA = this.a.toExp()
    val expB = this.b.toExp()
    (expA.typ, expB.typ) match {
      case (viper.silver.ast.Perm, viper.silver.ast.Perm) => PermMul(expA, expB)()
      case (viper.silver.ast.Int, viper.silver.ast.Perm) => IntPermMul(expA, expB)()
      case (viper.silver.ast.Perm, viper.silver.ast.Int) => IntPermMul(expB, expA)()
      case (viper.silver.ast.Int, viper.silver.ast.Int) => Mul(expA, expB)()
      case _ => throw new IllegalArgumentException(s"Unknown combination of types in multiplication: ${expA.typ}  *  ${expB.typ}")
    }
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
    s"(${this.a.pretty()} - ${this.b.pretty()})"
  }

  override def toExp(): Exp = Sub(this.a.toExp(), this.b.toExp())()
}

case class VarTerm(name: String, typ: Type) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    s"${this.name}"
  }

  override def toExp(): Exp = LocalVar(this.name, this.typ)()

  override def scale(f: Term): LogicTerm = this
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

  override def toExp(): FieldAccess = FieldAccess(this.src.toExp(), Field(this.field, this.typ)())()
}

trait LogicTerm extends Term {
  def and(other: LogicTerm): LogicTerm = {
    AndTerm(this, other)
  }

  def or(other: LogicTerm): LogicTerm = {
    OrTerm(this, other)
  }

  def scale(f: Term): LogicTerm
}

case class BoolTerm(value: Boolean) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(this)
  }

  def pretty(): String = {
    s"${this.value}"
  }

  override def toExp(): Exp = BoolLit(this.value)()

  override def scale(f: Term): LogicTerm = this
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

  override def toExp(): Exp = And(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this.a.scale(f).and(this.b.scale(f))
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

  override def toExp(): Exp = Or(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this.a.scale(f).or(this.b.scale(f))
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

  override def toExp(): Exp = Not(this.t.toExp())()

  override def scale(f: Term): LogicTerm = NotTerm(this.t.scale(f))
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

  override def toExp(): Exp = Implies(this.prem.toExp(), this.cons.toExp())()

  def rewrite(ts: TermSub): ImplTerm = {
    ImplTerm(
      this.prem.substitute(ts).asInstanceOf[LogicTerm],
      this.cons.substitute(ts).asInstanceOf[LogicTerm]
    )
  }

  def scale(f: Term): ImplTerm = {
    ImplTerm(this.prem, this.cons.scale(f))
  }
}

trait Comparison {
  def negate(): Comparison

  def pretty(): String

  def subst(ts: TermSub): Comparison

  def toLogicTerm(): LogicTerm
}

case class EqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(EqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison = {
    EqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }

  def pretty(): String = {
    s"${this.a.pretty()} == ${this.b.pretty()}"
  }

  override def negate(): Comparison = NotEqCmpTerm(this.a, this.b)

  override def toLogicTerm(): LogicTerm = this

  override def toExp(): Exp = EqCmp(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this
}

case class NotEqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(NotEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison = {
    NotEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} != ${this.b.pretty()}"
  }

  override def negate(): Comparison = EqCmpTerm(this.a, this.b)

  override def toLogicTerm(): LogicTerm = this

  override def toExp(): Exp = NeCmp(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this
}

case class LessCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(LessCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison = {
    LessCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} <  ${this.b.pretty()}"
  }

  override def negate(): Comparison = GreaterEqCmpTerm(this.a, this.b)

  override def toLogicTerm(): LogicTerm = this

  override def toExp(): Exp = LtCmp(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this
}

case class LessEqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(LessEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }


  def subst(ts: TermSub): Comparison = {
    LessEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} <= ${this.b.pretty()}"
  }

  override def negate(): Comparison = GreaterCmpTerm(this.a, this.b)

  override def toLogicTerm(): LogicTerm = this

  override def toExp(): Exp = LeCmp(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this
}

case class GreaterCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(GreaterCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison = {
    GreaterCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} >  ${this.b.pretty()}"
  }

  override def negate(): Comparison = LessEqCmpTerm(this.a, this.b)

  override def toLogicTerm(): LogicTerm = this

  override def toExp(): Exp = GtCmp(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this
}

case class GreaterEqCmpTerm(a: Term, b: Term) extends LogicTerm with Comparison {
  def substitute(ts: TermSub): Term = {
    ts.apply(GreaterEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    ))
  }

  def subst(ts: TermSub): Comparison = {
    GreaterEqCmpTerm(
      this.a.substitute(ts),
      this.b.substitute(ts)
    )
  }


  def pretty(): String = {
    s"${this.a.pretty()} >= ${this.b.pretty()}"
  }

  override def negate(): Comparison = LessCmpTerm(this.a, this.b)

  override def toLogicTerm(): LogicTerm = this

  override def toExp(): Exp = GeCmp(this.a.toExp(), this.b.toExp())()

  override def scale(f: Term): LogicTerm = this
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

  override def toExp(): Exp = PredicateAccessPredicate(
    PredicateAccess(this.pred.args.map(a => a.toExp()), this.pred.name)(),
    Some(this.perm.toExp())
  )()

  def rewrite(ts: TermSub): PredInstAccTerm = {
    PredInstAccTerm(
      PredInst(
        this.pred.name,
        this.pred.args.map(a => a.substitute(ts))
      ),
      this.perm.substitute(ts)
    )
  }
}

case class PredFieldAccTerm(exp: FieldAccTerm, perm: Term) extends LogicTerm {
  def substitute(ts: TermSub): Term = {
    ts.apply(PredFieldAccTerm(
      FieldAccTerm(
        this.exp.src.substitute(ts),
        this.exp.field,
        this.exp.typ
      ),
      this.perm.substitute(ts)
    ))
  }

  def scale(f: Term): PredFieldAccTerm = {
    PredFieldAccTerm(this.exp, MulTerm(this.perm, f))
  }

  def pretty(): String = {
    s"acc(${this.exp.pretty()}, ${this.perm.pretty()})"
  }

  override def toExp(): Exp = FieldAccessPredicate(
    this.exp.toExp(),
    Some(this.perm.toExp())
  )()

  def rewrite(ts: TermSub): PredFieldAccTerm = {
    PredFieldAccTerm(
      FieldAccTerm(
        this.exp.src.substitute(ts),
        this.exp.field,
        this.exp.typ
      ), this.perm.substitute(ts))
  }
}

// TODO: the magic wand could be generalized?!
//       - more general precondition (instead of sets of direct/folded permissions)
//       - more general body instead of explicitly forcing a single PredInstAccTerm
case class BaguetteMagic(directPrem: Set[PredFieldAccTerm], foldedPrem: Set[PredInstAccTerm], partialPrem: Set[ImplTerm], directCons: Set[PredFieldAccTerm], foldedCons: Set[PredInstAccTerm], partialCons: Set[ImplTerm]) extends LogicTerm {

  def premTerms(): Set[LogicTerm] = {
    this.directPrem.asInstanceOf[Set[LogicTerm]].union(this.foldedPrem.asInstanceOf[Set[LogicTerm]]).union(this.partialPrem.asInstanceOf[Set[LogicTerm]])
  }

  def consTerms(): Set[LogicTerm] = {
    this.directCons.asInstanceOf[Set[LogicTerm]].union(this.foldedCons.asInstanceOf[Set[LogicTerm]]).union(this.partialCons.asInstanceOf[Set[LogicTerm]])
  }

  def pretty(): String = {
    val cond = premTerms().map(_.pretty()).mkString(" && ")
    val cons = consTerms().map(_.pretty()).mkString(" && ")
    s"${cond} --* ${cons}"
  }

  def rewrite(ts: TermSub): BaguetteMagic = {
    val dirsPrem = this.directPrem.map(d => d.rewrite(ts))
    val folsPrem = this.foldedPrem.map(f => f.rewrite(ts))
    val partPrem = this.partialPrem.map(f => f.rewrite(ts))
    val dirsCons = this.directCons.map(d => d.rewrite(ts))
    val folsCons = this.foldedCons.map(f => f.rewrite(ts))
    val partCons = this.partialCons.map(f => f.rewrite(ts))
    BaguetteMagic(dirsPrem, folsPrem, partPrem, dirsCons, folsCons, partCons)
  }

  def scale(f: Term): BaguetteMagic = {
    val dirsPrem = this.directPrem.map(d => d.scale(f))
    val folsPrem = this.foldedPrem.map(d => d.scale(f))
    val partPrem = this.partialPrem.map(d => d.scale(f))
    val dirsCons = this.directCons.map(d => d.scale(f))
    val folsCons = this.foldedCons.map(f => f.scale(f))
    val partCons = this.partialCons.map(f => f.scale(f))
    BaguetteMagic(dirsPrem, folsPrem, partPrem, dirsCons, folsCons, partCons)
  }


  override def substitute(ts: TermSub): Term = {
    val dirsPrem = this.directPrem.map(d => d.substitute(ts).asInstanceOf[PredFieldAccTerm])
    val folsPrem = this.foldedPrem.map(f => f.substitute(ts).asInstanceOf[PredInstAccTerm])
    val partPrem = this.partialPrem.map(f => f.substitute(ts).asInstanceOf[ImplTerm])
    val dirsCons = this.directCons.map(d => d.substitute(ts).asInstanceOf[PredFieldAccTerm])
    val folsCons = this.foldedCons.map(f => f.substitute(ts).asInstanceOf[PredInstAccTerm])
    val partCons = this.partialCons.map(f => f.substitute(ts).asInstanceOf[ImplTerm])
    BaguetteMagic(dirsPrem, folsPrem, partPrem, dirsCons, folsCons, partCons)
  }

  override def toExp(): Exp = {
    val prem = premTerms()
      .map(v => v.toExp())
      .reduceLeftOption((a, b) => And(a, b)())
      .getOrElse(BoolLit(b = true)())
    val cons = consTerms()
      .map(v => v.toExp())
      .reduceLeftOption((a, b) => And(a, b)())
      .getOrElse(BoolLit(b = true)())
    MagicWand(prem, cons)()
  }
}

object TermRewriter {

  private def pushNegDown: Seq[TermSub] = Seq(
    FuncTermSub {
      case NegTerm(AddTerm(a, b)) => AddTerm(NegTerm(a), NegTerm(b))
      case c => c
    }
  )

  private def condSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case CondTerm(c, a, b) if c.equals(BoolTerm(true)) => a
      case CondTerm(c, a, b) if c.equals(BoolTerm(false)) => b
      case c => c
    }
  )

  private def compSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case LessEqCmpTerm(PermFracTerm(IntTerm(a), IntTerm(b)), PermFracTerm(IntTerm(c), IntTerm(d))) => {
        val fracA = a.doubleValue / b.doubleValue
        val fracB = c.doubleValue / d.doubleValue
        BoolTerm(fracA <= fracB)
      }
      case c => c
    }
  )

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

  private def addZeroSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case AddTerm(PermFracTerm(IntTerm(a), _), d) if a == BigInt.int2bigInt(0) => d
      case AddTerm(d, PermFracTerm(IntTerm(a), _)) if a == BigInt.int2bigInt(0) => d
      case c => c
    }
  )

  private def mulOneSimp: Seq[TermSub] = Seq(
    FuncTermSub {
      case MulTerm(PermFracTerm(IntTerm(a), IntTerm(b)), d) if a == BigInt.int2bigInt(1) && b == BigInt.int2bigInt(1) => d
      case MulTerm(d, PermFracTerm(IntTerm(a), IntTerm(b))) if a == BigInt.int2bigInt(1) && b == BigInt.int2bigInt(1) => d
      case c => c
    }
  )

  private def normConstFracTerm: Seq[TermSub] = Seq(
    FuncTermSub {
      case PermFracTerm(IntTerm(a), IntTerm(b)) if !(a.gcd(b).equals(BigInt.int2bigInt(1))) => {
        val g = a.gcd(b)
        PermFracTerm(IntTerm(a / g), IntTerm(b / g))
      }
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

  private def addNegSelf: Seq[TermSub] = Seq(
    FuncTermSub {
      case AddTerm(a, NegTerm(b)) if a.equals(b) => PermFracTerm(IntTerm(BigInt.int2bigInt(0)), IntTerm(BigInt.int2bigInt(1)))
      case AddTerm(NegTerm(b), a) if a.equals(b) => PermFracTerm(IntTerm(BigInt.int2bigInt(0)), IntTerm(BigInt.int2bigInt(1)))
      case c => c
    }
  )

  def simplify(t: Term): Term = {

    val subs = Seq(
      pushNegDown,
      condSimp,
      compSimp,
      addNegSelf,
      addZeroSimp,
      mulOneSimp,
      normConstFracTerm,
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

object LogicTermRewriting {
  private def simpConj: Seq[TermSub] = Seq(
    FuncTermSub {
      case AndTerm(BoolTerm(true), b) => b
      case AndTerm(b, BoolTerm(true)) => b
      case AndTerm(BoolTerm(false), _) => BoolTerm(false)
      case AndTerm(_, BoolTerm(false)) => BoolTerm(false)
      case c => c
    }
  )

  private def simpDisj: Seq[TermSub] = Seq(
    FuncTermSub {
      case OrTerm(BoolTerm(false), b) => b
      case OrTerm(b, BoolTerm(false)) => b
      case OrTerm(BoolTerm(true), _) => BoolTerm(true)
      case OrTerm(_, BoolTerm(true)) => BoolTerm(true)
      case c => c
    }
  )

  private def simpEquiv: Seq[TermSub] = Seq(
    FuncTermSub {
      case EqCmpTerm(a, b) if a.equals(b) => BoolTerm(true)
      case NotEqCmpTerm(a, b) if a.equals(b) => BoolTerm(false)
      case c => c
    }
  )


  private def containsLT(term: Term, pattern: LogicTerm): Boolean = {
    term match {
      case lt: LogicTerm => {
        if (term.equals(pattern)) {
          true
        }
        else {
          lt match {
            case AndTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case BaguetteMagic(directPrem, foldedPrem, partialPrem, directCons, foldedCons, partialCons) => {
              directPrem.exists(a => containsLT(a, pattern)) ||
                foldedPrem.exists(a => containsLT(a, pattern)) ||
                partialPrem.exists(a => containsLT(a, pattern)) ||
                directCons.exists(a => containsLT(a, pattern)) ||
                foldedCons.exists(a => containsLT(a, pattern)) ||
                partialCons.exists(a => containsLT(a, pattern))
            }
            case BoolTerm(value) => false
            case EqCmpTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case GreaterCmpTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case GreaterEqCmpTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case ImplTerm(prem, cons) => containsLT(prem, pattern) || containsLT(cons, pattern)
            case LessCmpTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case LessEqCmpTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case NotEqCmpTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case NotTerm(t) => false
            case OrTerm(a, b) => containsLT(a, pattern) || containsLT(b, pattern)
            case PredFieldAccTerm(exp, perm) => containsLT(exp, pattern) || containsLT(perm, pattern)
            case PredInstAccTerm(pred, perm) => pred.args.exists(a => containsLT(a, pattern)) || containsLT(perm, pattern)
            case VarTerm(name, typ) => false
            case _ => false
          }
        }
      }
      case _ => false
    }
  }

  private def collectApplicable(lt: LogicTerm): Option[(Term, Term)] = {
    lt match {
      case AndTerm(a, b) => collectApplicable(a).orElse(collectApplicable(b))
      case _: BaguetteMagic => None
      case BoolTerm(value) => None
      case EqCmpTerm(v@VarTerm(n, _), b) if n.startsWith("t$") && !containsLT(b, v) => Some((v, b))
      case EqCmpTerm(a, b) => None
      case GreaterCmpTerm(a, b) => None
      case GreaterEqCmpTerm(a, b) => None
      case ImplTerm(prem, cons) => None
      case LessCmpTerm(a, b) => None
      case LessEqCmpTerm(a, b) => None
      case NotEqCmpTerm(a, b) => None
      case NotTerm(t) => None
      case OrTerm(a, b) => None
      case PredFieldAccTerm(exp, perm) => None
      case PredInstAccTerm(pred, perm) => None
      case VarTerm(name, typ) => None
      case _ => None
    }
  }

  def simplify(t: LogicTerm): LogicTerm = {
    // to use this for a simplification of the knowledge base the info about the values in the heap needs to be retained compared to just simplifying to true :)
    // collect the equivalences and process a knowledge base afterward
    val subs = Seq(
      simpConj,
      simpDisj,
      simpEquiv
    ).flatten
    val func = FuncTermSub(f => {
      subs.foldLeft(f)((v, q) => v.substitute(q))
    })
    FixedPoint.compute(t, (q: LogicTerm) => {
      val res = FixedPoint.compute(q, (p: LogicTerm) => p.substitute(func).asInstanceOf[LogicTerm])
      val fp = FixedPoint.compute(res, (t: LogicTerm) => {
        val repl = collectApplicable(t)
        repl.map(r => t.substitute(MapTermSub(Map((r._1, r._2)))).asInstanceOf[LogicTerm]).getOrElse(t)
      })
      fp
    })
  }

  def untangle(kb: KnowledgeBase): KnowledgeBase = {
    // to use this for a simplification of the knowledge base the info about the values in the heap needs to be retained compared to just simplifying to true :)
    // collect the equivalences and process a knowledge base afterward
    val subs = Seq(
      simpConj,
      simpDisj,
      simpEquiv
    ).flatten
    val func = FuncTermSub(f => {
      subs.foldLeft(f)((v, q) => v.substitute(q))
    })

    var replacements = Seq[(Term, Term)]()
    var current = kb.info
    var running = true
    while (running) {
      val res = FixedPoint.compute(current, (p: LogicTerm) => p.substitute(func).asInstanceOf[LogicTerm])
      val fp = FixedPoint.compute((res, Seq[(Term, Term)]()), (acc: (LogicTerm, Seq[(Term, Term)])) => {
        val (t, s) = acc
        val repl = collectApplicable(t)
        repl match {
          case Some(r) => {
            val res = t.substitute(MapTermSub(Map((r._1, r._2)))).asInstanceOf[LogicTerm]
            (res, s ++ Seq(r))
          }
          case None => acc
        }
      })

      running = !fp._1.equals(current)
      current = fp._1
      replacements = replacements ++ fp._2
    }

    //    println(s"REPLACEMENTS DURING UNTANGLE:")
    //    replacements.foreach(a => println(s"${a._1.pretty()} => ${a._2.pretty()}"))
    //    println(s"RESULT INFO: ${current.pretty()}")

    // TODO: having two variables that are later discovered to be equal
    //       will result in inconsistent state within the fields of the object
    //       is this a practical problem?

    val allRefsInHeap = kb.heap.objMap.keySet.map(a => (a, a.toVarTerm(Ref)))
    val allRefsFromFields = kb.heap.objMap.values.flatMap(o => o.fields.map(e => (e._2, e._2.toVarTerm(kb.fieldTypes(e._1))))).toSet
    val allRefsInAssignment = kb.assignment.variables.values.map(e => (e._1, e._1.toVarTerm(e._2))).toSet
    val allRefs = allRefsInHeap.union(allRefsFromFields).union(allRefsInAssignment)
//    allRefs.foreach(a => println(s"${a._1.pretty()}   ${a._2.pretty()}"))

    val sub = MapTermSub(replacements.toMap)
    val mapping: (Map[ValRef, ValRef], LogicTerm) = allRefs.foldLeft((Map[ValRef, ValRef](), BoolTerm(true).asInstanceOf[LogicTerm]))((acc, e) => {
      val result = FixedPoint.compute(e._2, (a: Term) => a.substitute(sub))
      result match {
        case VarTerm(name, typ) if (name.startsWith("t$")) =>
          val ref = ValRef(Integer.parseInt(name.substring(2)))
          (acc._1.updated(e._1, ref), acc._2)
        case t => {
          val fresh = kb.assignment.rc.freshValRef()
          (acc._1.updated(e._1, fresh), acc._2.and(EqCmpTerm(fresh.toVarTerm(e._2.typ), t)))
        }
      }
    })

    val refReplacement = (v: ValRef) => mapping._1.getOrElse(v, v)
    val updatedAssignment = Assignment(
      kb.assignment.rc,
      kb.assignment.variables.map(e => {
        (e._1, (refReplacement(e._2._1), e._2._2))
      })
    )

    val updatedPartial = Potential(
      kb.partial.partial.map(p => {
        val mappedPrem = FixedPoint.compute(p.prem, (a: Term) => LogicTermRewriting.simplify(a.substitute(sub).asInstanceOf[LogicTerm]))
        val mappedCons = FixedPoint.compute(p.cons, (a: Term) => LogicTermRewriting.simplify(a.substitute(sub).asInstanceOf[LogicTerm]))
        ImplTerm(mappedPrem, mappedCons)
      })
    )

    val updatedMWM = MagicWandManager(kb.mwm.wands.map(w => {
      FixedPoint.compute(w, (a: BaguetteMagic) => a.rewrite(sub))
    }))

    val updatedHeap = Heap(
      kb.heap.rc,
      (kb.heap.initialized._1.map(refReplacement),
        kb.heap.initialized._2.map(t => (refReplacement(t._1), t._2, refReplacement(t._3)))),
      kb.heap.objMap.map(e => {
        val self = refReplacement(e._1)
        val obj = Obj(self,
          e._2.fields.map(f => (f._1, refReplacement(f._2))))
        (self, obj)
      })
    )

    val updatedInfo = mapping._2

    val updatedFolded = FoldedPermissionMask(kb.folded.permissions.map(e => {
      val mappedPerm = FixedPoint.compute(e._2, (a: Term) => TermRewriter.simplify(a.substitute(sub)))
      val mappedArgs = e._1.args.map(q => {
        FixedPoint.compute(q, (a: Term) => a.substitute(sub))
      })
      val inst = PredInst(e._1.name, mappedArgs)
      (inst, mappedPerm)
    }))

    val updatedDirect = DirectPermissionMask(kb.direct.permissions.map(e => {
      val mappedSrc = FixedPoint.compute(e._1.src, (a: Term) => TermRewriter.simplify(a.substitute(sub)))
      val mappedPerm = FixedPoint.compute(e._2, (a: Term) => TermRewriter.simplify(a.substitute(sub)))
      val fa = FieldAccTerm(mappedSrc, e._1.field, e._1.typ)
      (fa, mappedPerm)
    }))

    KnowledgeBase(
      kb.path,
      updatedAssignment,
      updatedHeap,
      updatedDirect,
      updatedFolded,
      updatedInfo,
      updatedPartial,
      updatedMWM,
      kb.fieldTypes
    )
  }

}