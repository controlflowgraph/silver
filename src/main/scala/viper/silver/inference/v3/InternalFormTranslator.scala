package viper.silver.inference.v3

import viper.silver.ast._
import viper.silver.inference.v3.ast._

object InternalFormTranslator {
  def transformSeqnToInternalForm(rep: InternalRepresentation, prev: Set[Ident], defs: Map[String, PredDef], seq: Seqn, inj: Option[Injection]): (Seqn, Set[Ident]) = {
    val transformed: (Seq[Stmt], Set[Ident]) = seq.ss.foldLeft((Seq[Stmt](), prev))((acc, s) => {
      val res = translateStmtToInternalForm(rep, acc._2, defs, s)

      (acc._1 ++ Seq(res._1), res._2)
    })
    val injection = inj match {
      case Some(value) => Seq(value)
      case None => Seq()
    }
    (Seqn(transformed._1 ++ injection, seq.scopedSeqnDeclarations)(), transformed._2)
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
      case v => throw new IllegalArgumentException(s"Unable to transform ${v.getClass.getCanonicalName} to logic term!")
    }
  }

  def translateStmtToInternalForm(rep: InternalRepresentation, prev: Set[Ident], defs: Map[String, PredDef], stmt: Stmt): (Stmt, Set[Ident]) = {
    stmt match {
      case NewStmt(lhs, fields) => {

        // TODO: rename the current target to some temporary variable value (the knowledge relating that)

        // inhaling access to the new location
        val mappedVar = VarTerm(lhs.name, lhs.typ)
        val mapped = fields.map(f => FieldAccTerm(mappedVar, f.name, f.typ))
          .map(f => PredFieldAccTerm(f, PermAmount.WRITE))
          .reduceOption[LogicTerm]((a, b) => AndTerm(a, b))
          .getOrElse(BoolTerm(true))

        val ln = rep.freshIdent()
        val line = InhaleLine(ln, mapped)

        rep.addLine(line)
        rep.addConnections(prev, ln)

        (stmt, Set(ln))
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

          rep.addLine(line)
          rep.addConnections(prev, ln)

          (Seqn(Seq(inj, stmt), Seq())(), Set(ln))
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

          rep.addLine(line)
          rep.addConnections(prev, ln)

          (Seqn(Seq(inj, stmt), Seq())(), Set(ln))
        }
      }
      case MethodCall(methodName, args, targets) => {
        //        MethodCallLine(
        //          targets.map(t => Var(t.name, t.typ)),
        //          methodName,
        //          args.map(a => expToTerm(a))
        //        )
        // TODO: remove knowledge about the passed arguments

        val inj = freshInjection()

        //        val meth = this.program.methods.find(m => m.name.equals(methodName))
        //          .get
        //
        //        val argRepl = meth.formalArgs.map(d => Var(d.name, d.typ)).zip(args.map(expToTerm))
        //
        //        val exhales = meth.pres.map(p => expToPredTerm(p))
        //          .map(t => t.substitute(TermSub(argRepl.toMap)))
        //          .map(v => ExhaleLine(inj, v))
        //
        //        val retRepl = meth.formalReturns.map(v => Var(v.name, v.typ)).zip(targets.map(v => Var(v.name, v.typ)))
        //
        //        val inhales = meth.posts.map(p => expToPredTerm(p))
        //          .map(t => t.substitute(TermSub((argRepl ++ retRepl).toMap)))
        //          .map(v => InhaleLine(v))
        //
        //        val reqs = this.program.inferInfo.typeAnnotations(methodName)
        //        val argNames = this.program.methods.filter(m => m.name.equals(methodName)).head.formalArgs.map(f => f.name)
        //        val paramedExhaling: Seq[ExhaleLine] = reqs._1.zip(argNames).flatMap(t => t._1 match {
        //          case dt: DatatypeType => {
        //            val name = encodeTypeAsString(dt)
        //            val term = PredImpl(Set(IsNonNull(Var(t._2, Ref))), PredPredAcc(PredInstance(name, Seq(Var(t._2, Ref)))))
        //            Seq(ExhaleLine(inj, term.substitute(TermSub((argRepl ++ retRepl).toMap))))
        //          }
        //          case _ => Seq()
        //        })
        //
        //        val retNames = this.program.methods.filter(m => m.name.equals(methodName)).head.formalReturns.map(f => f.name)
        //        val paramedInhaling = reqs._2.zip(retNames).flatMap(t => t._1 match {
        //          case dt: DatatypeType => {
        //            val name = encodeTypeAsString(dt)
        //            val term = PredPredAcc(PredInstance(name, Seq(Var(t._2, Ref))))
        //            Seq(InhaleLine(term.substitute(TermSub(argRepl.toMap))))
        //          }
        //          case _ => Seq()
        //        })
        //
        //        val line = Sequence(((paramedExhaling ++ exhales).reverse) ++ paramedInhaling ++ inhales)
        //        println(s"LINE FOR METH CALL: ${line}")

        val ln = rep.freshIdent()
        val line = CallLine(ln, inj, methodName, targets.map(v => VarTerm(v.name, v.typ)), args.map(expToTerm))

        rep.introduce(prev, line)

        (Seqn(Seq(inj, stmt), Seq())(), Set(ln))
      }
      case Exhale(exp) => {
        val inj = freshInjection()
        val ln = rep.freshIdent()
        val line = ExhaleLine(ln, inj, expToLogicTerm(exp))

        rep.introduce(prev, line)

        (Seqn(Seq(inj, stmt), Seq())(), Set(ln))
      }
      case Inhale(exp) => {
        val ln = rep.freshIdent()
        val line = InhaleLine(ln, expToLogicTerm(exp))
        rep.introduce(prev, line)
        (stmt, Set(ln))
      }
      case Assert(exp) => {
        val ln = rep.freshIdent()
        val inj = freshInjection()
        val line = AssertLine(ln, inj, expToLogicTerm(exp))

        rep.introduce(prev, line)

        (Seqn(Seq(inj, stmt), Seq())(), Set(ln))
      }
      case Assume(exp) => {
        val ln = rep.freshIdent()
        val line = AssumeLine(ln, expToLogicTerm(exp))
        rep.introduce(prev, line)
        (stmt, Set(ln))
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
        rep.introduce(Set(exLn), in)


        (Seqn(Seq(inj, stmt), Seq())(), Set(inLn))
      }
      case Unfold(acc) => {
        val inj = freshInjection()

        val inst = instantiatePredicateFolding(defs, acc)
        val body = inst._2
        val folded = inst._1


        val exLn = rep.freshIdent()
        val ex = ExhaleLine(exLn, inj, body)
        val inLn = rep.freshIdent()
        val in = InhaleLine(inLn, folded)

        rep.introduce(prev, ex)
        rep.introduce(Set(exLn), in)

        (Seqn(Seq(inj, stmt), Seq())(), Set(inLn))
      }

      case seq: Seqn => transformSeqnToInternalForm(rep, prev, defs, seq, None)
      case i@If(cond, thn, els) => {

        // TODO: potentially split the condition into pred term and knowledge set
        val translatedCondition = expToLogicTerm(cond)
        val inj = freshInjection()

        val ln = rep.freshIdent()

        val line = BranchLine(
          ln,
          inj,
          translatedCondition
        )

        rep.introduce(prev, line)

        // TODO: maybe remove the injections at this point since they should be covered by the pre cond inj
        val firstInj = freshInjection()
        val secondInj = freshInjection()
        val thnTrans = transformSeqnToInternalForm(rep, Set(ln), defs, thn, Some(firstInj))
        val elsTrans = transformSeqnToInternalForm(rep, Set(ln), defs, els, Some(secondInj))

        val transIf = If(cond, thnTrans._1, elsTrans._1)(i.pos, i.info, i.errT)

        (Seqn(Seq(inj, transIf), Seq())(), thnTrans._2.union(elsTrans._2))
      }
    }
  }

  def instantiatePredicateFolding(defs: Map[String, PredDef], pred: PredicateAccessPredicate): (LogicTerm, LogicTerm) = {
    (???, ???)
  }
}
