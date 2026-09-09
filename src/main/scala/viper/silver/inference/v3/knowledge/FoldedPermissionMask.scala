package viper.silver.inference.v3.knowledge

import viper.silver.inference.v3.ast.{AddTerm, IntTerm, PermFracTerm, PredInst, PredInstAccTerm, SubTerm, Term, TermRewriter, TermSub}

case class FoldedPermissionMask(permissions: Map[PredInst, Term]) {
  def this() = {
    this(Map())
  }

  def inhale(b: PredInstAccTerm): FoldedPermissionMask = {
    val current = this.permissions.getOrElse(b.pred, PermFracTerm(IntTerm(0), IntTerm(1)))
    val amount = TermRewriter.simplify(AddTerm(current, b.perm))
    FoldedPermissionMask(
      this.permissions.updated(b.pred, amount)
    )
  }

  def pretty(): String = {
    this.permissions.map(e => s"${e._1.pretty()}: ${e._2.pretty()}").mkString("\n")
  }

  def exhale(pa: PredInstAccTerm): FoldedPermissionMask = {
    exhale(pa.pred, pa.perm)
  }

  def exhale(pred: PredInst, perm: Term): FoldedPermissionMask = {
    val current = this.permissions.getOrElse(pred, PermFracTerm(IntTerm(0), IntTerm(1)))
    val amount = TermRewriter.simplify(SubTerm(current, perm))
    FoldedPermissionMask(
      this.permissions.updated(pred, amount)
    )
  }

  def substitute(ts: TermSub): FoldedPermissionMask = {
    FoldedPermissionMask(
      this.permissions.map(e => (
        PredInst(e._1.name, e._1.args.map(a => a.substitute(ts))),
        e._2.substitute(ts)
      ))
    )
  }

  def getAmount(pred: PredInst): Term = {
    this.permissions.getOrElse(pred, PermFracTerm(IntTerm(0), IntTerm(1)))
  }
}