package viper.silver.inference.v3

import viper.silver.ast._
import viper.silver.inference.v3.ast._

object InternalFormTranslator {
  def transformSeqnToInternalForm(rep: InternalRepresentation, prev: Ident, defs: Map[String, PredDef], seq: Seqn, inj: Option[Injection]): (Seqn, Ident, Ident) = {
    val transformed: (Seq[Stmt], Ident, Seq[Ident]) = seq.ss.foldLeft((Seq[Stmt](), prev, Seq[Ident]()))((acc, s) => {
      val res = translateStmtToInternalForm(rep, acc._2, defs, s)

      (acc._1 ++ Seq(res._1), res._2, acc._3 ++ Seq(res._3))
    })
    val injection = inj match {
      case Some(value) => Seq(value)
      case None => Seq()
    }
    if(transformed._1.isEmpty){
      val ln = rep.freshIdent()
      val line = AssumeLine(ln, BoolTerm(true))

      rep.introduce(prev, line)

      (Seqn(injection, seq.scopedSeqnDeclarations)(), ln, ln)
    }
    else{
      (Seqn(transformed._1 ++ injection, seq.scopedSeqnDeclarations)(), transformed._3.head, transformed._3.last)
    }
  }

  private var injectionId = 0

  def freshInjection(): Injection = {
    val inj = Injection(injectionId)()
    injectionId += 1
    inj
  }

  def expToTerm(exp: Exp): Term = {
    exp match {
      case fa: FieldAccess => FieldAccTerm(expToTerm(fa.rcv), fa.field.name, fa.field.typ)
      case lit: NullLit => NullTerm()
      case lit: IntLit => IntTerm(lit.i)
      case lv: LocalVar => VarTerm(lv.name, lv.typ)
      case add: Add => AddTerm(expToTerm(add.left), expToTerm(add.right))
      case add: Sub => SubTerm(expToTerm(add.left), expToTerm(add.right))
      case frac: FractionalPerm => PermFracTerm(expToTerm(frac.left), expToTerm(frac.right))
      case _: EqCmp => expToLogicTerm(exp)
      case _: NeCmp => expToLogicTerm(exp)
      case _: LtCmp => expToLogicTerm(exp)
      case _: LeCmp => expToLogicTerm(exp)
      case _: GtCmp => expToLogicTerm(exp)
      case _: GeCmp => expToLogicTerm(exp)
      case _: BoolLit => expToLogicTerm(exp)
      case _: Not => expToLogicTerm(exp)
      case _: And => expToLogicTerm(exp)
      case _: Or => expToLogicTerm(exp)
      case _: Implies => expToLogicTerm(exp)
      case _: FieldAccessPredicate => expToLogicTerm(exp)
      case _: PredicateAccessPredicate => expToLogicTerm(exp)
      case _: Unfolding => expToLogicTerm(exp)
      case _: FullPerm => PermFracTerm(IntTerm(1), IntTerm(1))
      case v => throw new IllegalArgumentException(s"Unable to transform ${v.getClass.getCanonicalName} to term!")
    }
  }

  def expToLogicTerm(exp: Exp): LogicTerm = {
    exp match {
      case lit: BoolLit => BoolTerm(lit.value)
      case lv: LocalVar => VarTerm(lv.name, lv.typ)
      case not: Not => NotTerm(expToLogicTerm(not.exp))
      case eq: EqCmp => EqCmpTerm(expToTerm(eq.left), expToTerm(eq.right))
      case eq: NeCmp => NotEqCmpTerm(expToTerm(eq.left), expToTerm(eq.right))
      case eq: LtCmp => LessCmpTerm(expToTerm(eq.left), expToTerm(eq.right))
      case eq: LeCmp => LessEqCmpTerm(expToTerm(eq.left), expToTerm(eq.right))
      case eq: GtCmp => GreaterCmpTerm(expToTerm(eq.left), expToTerm(eq.right))
      case eq: GeCmp => GreaterEqCmpTerm(expToTerm(eq.left), expToTerm(eq.right))
      case and: And => AndTerm(expToLogicTerm(and.left), expToLogicTerm(and.right))
      case or: Or => OrTerm(expToLogicTerm(or.left), expToLogicTerm(or.right))
      case impl: Implies => ImplTerm(expToLogicTerm(impl.left), expToLogicTerm(impl.right))
      case acc: FieldAccessPredicate => PredFieldAccTerm(expToTerm(acc.loc).asInstanceOf[FieldAccTerm], expToTerm(acc.perm))
      case acc: PredicateAccessPredicate => PredInstAccTerm(PredInst(acc.loc.predicateName, acc.loc.args.map(expToTerm)), expToTerm(acc.perm))
      // TODO: support unfolding instructions
      case uf: Unfolding => BoolTerm(true)
      case v => throw new IllegalArgumentException(s"Unable to transform ${v.getClass.getCanonicalName} to logic term! ${exp}")
    }
  }

  def translateStmtToInternalForm(rep: InternalRepresentation, prev: Ident, defs: Map[String, PredDef], stmt: Stmt): (Stmt, Ident, Ident) = {
    stmt match {
      case NewStmt(lhs, fields) => {

        // TODO: rename the current target to some temporary variable value (the knowledge relating that)

        // inhaling access to the new location
        val mappedVar = VarTerm(lhs.name, lhs.typ)
        val mappedFields = fields.map(f => (f.name, f.typ))

        val ln = rep.freshIdent()
        val line = NewObjLine(ln, mappedVar, mappedFields)

        rep.addLine(line)
        rep.addConnection(prev, ln)

        (stmt, ln, ln)
      }
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) => {
          val inj = freshInjection()
          val ln = rep.freshIdent()
          val line = LocalAssignLine(
            ln,
            inj,
            VarTerm(lhs.name, lhs.typ),
            expToTerm(rhs)
          )

          rep.introduce(prev, line)

          (Seqn(Seq(inj, stmt), Seq())(), ln, ln)
        }
        case FieldAssign(lhs, rhs) => {
          val inj = freshInjection()
          val ln = rep.freshIdent()
          val line = FieldAssignLine(
            ln,
            inj,
            FieldAccTerm(expToTerm(lhs.rcv), lhs.field.name, lhs.typ),
            expToTerm(rhs)
          )

          rep.introduce(prev, line)

          (Seqn(Seq(inj, stmt), Seq())(), ln, ln)
        }
      }
      case MethodCall(methodName, args, targets) => {
        val inj = freshInjection()
        val ln = rep.freshIdent()
        val line = CallLine(ln, inj, methodName, targets.map(v => VarTerm(v.name, v.typ)), args.map(expToTerm))

        rep.introduce(prev, line)

        (Seqn(Seq(inj, stmt), Seq())(), ln, ln)
      }
      case Exhale(exp) => {
        val inj = freshInjection()
        val ln = rep.freshIdent()
        val line = ExhaleLine(ln, inj, expToLogicTerm(exp))

        rep.introduce(prev, line)

        (Seqn(Seq(inj, stmt), Seq())(), ln, ln)
      }
      case Inhale(exp) => {
        val ln = rep.freshIdent()
        val line = InhaleLine(ln, expToLogicTerm(exp))
        rep.introduce(prev, line)
        (stmt, ln, ln)
      }
      case Assert(exp) => {
        val ln = rep.freshIdent()
        val inj = freshInjection()
        val line = AssertLine(ln, inj, expToLogicTerm(exp))

        rep.introduce(prev, line)

        (Seqn(Seq(inj, stmt), Seq())(), ln, ln)
      }
      case Assume(exp) => {
        val ln = rep.freshIdent()
        val line = AssumeLine(ln, expToLogicTerm(exp))
        rep.introduce(prev, line)
        (stmt, ln, ln)
      }
      case Fold(acc) => {
        val inj = freshInjection()

        val inst = instantiatePredicateFolding(defs, acc)
        val body = inst._2
        val folded = inst._1

        val exLn = rep.freshIdent()
        val ex = ExhaleLine(exLn, inj, body)
        val inLn = rep.freshIdent()
        val in = InhaleLine(inLn, folded)

        rep.introduce(prev, ex)
        rep.introduce(exLn, in)


        (Seqn(Seq(inj, stmt), Seq())(), exLn, inLn)
      }
      case Unfold(acc) => {
        val inj = freshInjection()

        val inst = instantiatePredicateFolding(defs, acc)
        val body = inst._2
        val folded = inst._1


        val exLn = rep.freshIdent()
        val ex = ExhaleLine(exLn, inj, folded)
        val inLn = rep.freshIdent()
        val in = InhaleLine(inLn, body)

        rep.introduce(prev, ex)
        rep.introduce(exLn, in)

        (Seqn(Seq(inj, stmt), Seq())(), exLn, inLn)
      }

      case seq: Seqn => transformSeqnToInternalForm(rep, prev, defs, seq, None)
      case i@If(cond, thn, els) => {

        // TODO: potentially split the condition into pred term and knowledge set
        val translatedCondition = expToLogicTerm(cond)
        val inj = freshInjection()

        val ln = rep.freshIdent()

        val postThnInj = freshInjection()
        val postElsInj = freshInjection()

        val thnTrans = transformSeqnToInternalForm(rep, ln, defs, thn, Some(postThnInj))
        val elsTrans = transformSeqnToInternalForm(rep, ln, defs, els, Some(postElsInj))

        val line = BranchLine(
          ln,
          inj,
          translatedCondition,
          thnTrans._2,
          elsTrans._2
        )

        rep.introduce(prev, line)

        val transIf = If(cond, thnTrans._1, elsTrans._1)(i.pos, i.info, i.errT)

        // introduce merge line
        val lastThn = thnTrans._3
        val lastEls = elsTrans._3

        val merg = rep.freshIdent()
        val merging = MergeLine(merg, ln, postThnInj, postElsInj, lastThn, lastEls)

        rep.addLine(merging)
        rep.addConnection(lastThn, merg)
        rep.addConnection(lastEls, merg)


        (Seqn(Seq(inj, transIf), Seq())(), ln, merg)
      }
    }
  }

  def instantiatePredicateFolding(defs: Map[String, PredDef], pred: PredicateAccessPredicate): (LogicTerm, LogicTerm) = {
    val predDef = defs(pred.loc.predicateName)
    val args = pred.loc.args.map(expToTerm)
    val init = predDef.params.zip(args).toMap
    // TODO: implement multiplication with permission amount when inhaling/exhaling (especially in the body)
    val ts = FuncTermSub {
      case v: VarTerm => init.getOrElse(v.name, v)
      case t => t
    }
    val instBody = predDef.body.substitute(ts).asInstanceOf[LogicTerm]
    val predInst = PredInst(predDef.name, args)
    (PredInstAccTerm(predInst, PermAmount.WRITE), instBody)
  }

  def processToInternalForm(defs: Map[String, PredDef], m: Method): InternalMethod = {
    val rep = new InternalRepresentation()
    val start = rep.freshIdent()
    val transform = InternalFormTranslator.transformSeqnToInternalForm(rep, start, defs, m.bodyOrAssumeFalse, None)

    val args = m.formalArgs.map(a => (a.name, a.typ))
    val res = m.formalReturns.map(a => (a.name, a.typ))

    val pres = m.pres.map(expToLogicTerm)
    val posts = m.posts.map(expToLogicTerm)

    InternalMethod(m.name, args, res, pres, posts, start, transform._3, rep, transform._1)
  }
}
