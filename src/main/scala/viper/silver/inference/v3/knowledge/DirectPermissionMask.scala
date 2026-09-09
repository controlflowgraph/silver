package viper.silver.inference.v3.knowledge

import viper.silver.inference.v3.ast.{AddTerm, FieldAccTerm, IntTerm, PermFracTerm, PredFieldAccTerm, SubTerm, Term, TermRewriter, TermSub}

case class DirectPermissionMask(permissions: Map[FieldAccTerm, Term]) {
  def this() = {
    this(Map())
  }

  def inhale(b: PredFieldAccTerm): DirectPermissionMask = {
    val before = this.permissions.getOrElse(b.exp, PermFracTerm(IntTerm(0), IntTerm(1)))
    val beforeSimp = AddTerm(before, b.perm)
    val afterSimp = TermRewriter.simplify(beforeSimp)
    DirectPermissionMask(
      this.permissions.updated(b.exp, afterSimp)
    )
  }

  def pretty(): String = {
    this.permissions.map(e => s"${e._1.pretty()}: ${e._2.pretty()}").mkString("\n")
  }

  def getAmount(pred: FieldAccTerm): Term = {
    this.permissions.getOrElse(pred, PermFracTerm(IntTerm(0), IntTerm(1)))
  }

  def substitute(ts: TermSub): DirectPermissionMask = {
    DirectPermissionMask(
      this.permissions.map(e => (
        FieldAccTerm(e._1.src.substitute(ts), e._1.field, e._1.typ),
        e._2.substitute(ts))
      )
    )
  }

  def exhale(b: PredFieldAccTerm): DirectPermissionMask = {
    val before = this.permissions.getOrElse(b.exp, PermFracTerm(IntTerm(0), IntTerm(1)))
    val beforeSimp = SubTerm(before, b.perm)
    val afterSimp = TermRewriter.simplify(beforeSimp)
    DirectPermissionMask(
      this.permissions.updated(b.exp, afterSimp)
    )
  }
}