package viper.silver.inference.v2

import viper.silver.ast._
import viper.silver.inference.v2.ast._
import viper.silver.inference.v2.knowledge.Knowledge.collectKnowledgeAboutTerm
import viper.silver.inference.v2.knowledge.{Equivalence, IsNonNull, IsNull, Knowledge, KnowledgeBase, SAT}

case class Infer(program: Program) {

  val searchDepth = 10

  def expToTerm(exp: Exp): Term = {
    exp match {
      case NullLit() => NullTerm(exp.typ)
      case LocalVar(name, typ) => Var(name, typ)
      case IntLit(value) => IntTerm(value, exp.typ)
      case FractionalPerm(left, right) => FracPerm(
        expToTerm(left),
        expToTerm(right),
        exp.typ
      )
      case FieldAccess(rcv, field) => FieldAcc(
        expToTerm(rcv),
        field.name,
        field.typ
      )
      case FalseLit() => BoolTerm(value = false, exp.typ)
      case TrueLit() => BoolTerm(value = true, exp.typ)
      case e => {
        throw new IllegalArgumentException(s"Unknown exp to convert to term ${e} ${e.getClass.getName}")
      }
    }
  }

  def expToKnowledge(exp: Exp): Set[Knowledge] = {
    exp match {
      case NeCmp(e, NullLit()) => Set(IsNonNull(expToTerm(e)))
      case EqCmp(e, NullLit()) => Set(IsNull(expToTerm(e)))
      case NeCmp(NullLit(), e) => Set(IsNonNull(expToTerm(e)))
      case EqCmp(NullLit(), e) => Set(IsNull(expToTerm(e)))
      case e => {
        throw new IllegalArgumentException(s"Unknown exp to convert to knowledge set ${e} ${e.getClass.getName}")
      }
    }
  }

  def expToPredTerm(exp: Exp): PredTerm = {
    exp match {
      case PredicateAccessPredicate(loc, _) => {
        PredPredAcc(PredInstance(loc.predicateName, loc.args.map(expToTerm)))
      }
      case And(a, b) => {
        PredAnd(expToPredTerm(a), expToPredTerm(b))
      }
      case _: NeCmp => PredTrue()
      case _: LeCmp => PredTrue()
      case _: Unfolding => PredTrue()
      case Implies(cond, body) => {
        PredImpl(expToKnowledge(cond), expToPredTerm(body))
      }
      case e => {
        throw new IllegalArgumentException(s"Unknown exp to convert to pred term ${e} ${e.getClass.getName}")
      }
    }
  }

  def transformSeqnToInternalForm(defs: Map[String, PredDef], seq: Seqn): (Seqn, Sequence) = {
    val transformed: Seq[(Stmt, Line)] = seq.ss.map(s => translateStmtToInternalForm(defs, s))
    (Seqn(transformed.map(_._1), seq.scopedSeqnDeclarations)(), Sequence(transformed.map(_._2)))
  }

  private var injectionId = 0

  def freshInjection(): Injection = {
    val inj = Injection(injectionId)()
    injectionId += 1
    inj
  }

  def translateStmtToInternalForm(defs: Map[String, PredDef], stmt: Stmt): (Stmt, Line) = {
    stmt match {
      case NewStmt(lhs, fields) => {

        // TODO: rename the current target to some temporary variable value (the knowledge relating that)

        // inhaling access to the new location
        val mappedVar = expToTerm(lhs)
        val mapped = fields.map(f => FieldAcc(mappedVar, f.name, f.typ))
          .map(f => PredFieldAcc(f))
          .reduceOption[PredTerm]((a, b) => PredAnd(a, b))
          .getOrElse(PredTrue())

        (stmt, InhaleLine(mapped))
      }
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) => {
          val inj = freshInjection()
          val line = VarAssignLine(
            inj,
            Var(lhs.name, lhs.typ),
            expToTerm(rhs)
          )

          (Seqn(Seq(inj, stmt), Seq())(), line)
        }
        case FieldAssign(lhs, rhs) => {
          val inj = freshInjection()
          val line = FieldAssignLine(
            inj,
            FieldAcc(expToTerm(lhs.rcv), lhs.field.name, lhs.typ),
            expToTerm(rhs)
          )
          (Seqn(Seq(inj, stmt), Seq())(), line)
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

        val meth = this.program.methods.find(m => m.name.equals(methodName))
          .get

        val argRepl = meth.formalArgs.map(d => Var(d.name, d.typ)).zip(args.map(expToTerm))

        val exhales = meth.pres.map(p => expToPredTerm(p))
          .map(t => t.substitute(TermSub(argRepl.toMap)))
          .map(v => ExhaleLine(inj, v))

        val retRepl = meth.formalReturns.map(v => Var(v.name, v.typ)).zip(targets.map(v => Var(v.name, v.typ)))

        val inhales = meth.posts.map(p => expToPredTerm(p))
          .map(t => t.substitute(TermSub((argRepl ++ retRepl).toMap)))
          .map(v => InhaleLine(v))

        val line = Sequence(exhales ++ inhales)
        (Seqn(Seq(inj, stmt), Seq())(), line)
      }
      case Exhale(exp) => {
        val inj = freshInjection()
        val line = ExhaleLine(inj, expToPredTerm(exp))
        (Seqn(Seq(inj, stmt), Seq())(), line)
      }
      case Inhale(exp) => (stmt, InhaleLine(expToPredTerm(exp)))
      case Assert(exp) => {
        val inj = freshInjection()
        val line = AssertLine(inj, expToPredTerm(exp))
        (Seqn(Seq(inj, stmt), Seq())(), line)
      }
      case Assume(exp) => (stmt, AssumeLine(expToPredTerm(exp), Knowledge.conditionToKnowledgeSet(exp)))
      case Fold(acc) => {
        val inj = freshInjection()

        val inst = instantiatePredicateFolding(defs, acc)
        val body = inst._2
        val folded = inst._1

        val line = Sequence(Seq(
          ExhaleLine(inj, body),
          InhaleLine(folded)
        ))

        (Seqn(Seq(inj, stmt), Seq())(), line)
      }
      case Unfold(acc) => {
        val inj = freshInjection()

        val inst = instantiatePredicateFolding(defs, acc)
        val body = inst._2
        val folded = inst._1


        val line = Sequence(Seq(
          ExhaleLine(inj, folded),
          InhaleLine(body)
        ))

        (Seqn(Seq(inj, stmt), Seq())(), line)
      }

      case seq: Seqn => transformSeqnToInternalForm(defs, seq)
      case i@If(cond, thn, els) => {

        // TODO: potentially split the condition into pred term and knowledge set
        val translatedCondition = expToPredTerm(cond)
        val knowledge = Knowledge.conditionToKnowledgeSet(cond)
        val inj = freshInjection()

        val thnTrans = transformSeqnToInternalForm(defs, thn)
        val elsTrans = transformSeqnToInternalForm(defs, els)

        val line = NonDetBranch(
          inj,
          thnTrans._2.prepend(AssumeLine(translatedCondition, knowledge)),
          elsTrans._2.prepend(AssumeLine(PredNot(translatedCondition), knowledge.map(_.negate()))),
        )

        val transIf = If(cond, thnTrans._1, elsTrans._1)(i.pos, i.info, i.errT)

        (Seqn(Seq(inj, transIf), Seq())(), line)
      }
    }
  }

  def instantiatePredicateFolding(defs: Map[String, PredDef], acc: PredicateAccessPredicate): (PredPredAcc, PredTerm) = {
    val pred = acc.loc

    // map the arguments of the predicate
    val terms = pred.args.map(a => expToTerm(a))

    // instantiate variables inside predicate
    val definition = defs(pred.predicateName)
    val init = VariableInstantiation(definition.params.zip(terms).toMap)
    val instantiated = definition.body.instantiate(init)

    // combine field access permissions
    // TODO: filter only the ones that are not 100% unsat (conservative)
    //       or the ones that are 100% sat (optimistic)
    val directExhale = instantiated.direct.map(d => PredFieldAcc(d._2))
      .reduceOption[PredTerm]((a, b) => PredAnd(a, b))
    // combine predicate permissions
    // TODO: same here as above for the filtering with knowledge
    val foldedExhale = instantiated.folded.map(d => PredPredAcc(d._2))
      .reduceOption[PredTerm]((a, b) => PredAnd(a, b))
    // combine field and predicate permissions
    val body = (directExhale, foldedExhale) match {
      case (Some(a), Some(b)) => PredAnd(a, b)
      case (None, Some(b)) => b
      case (Some(a), None) => a
      case (None, None) => PredTrue()
    }

    val folded = PredPredAcc(PredInstance(pred.predicateName, terms))
    (folded, body)
  }

  def collectContainedPermissions(pt: PredTerm): Set[PredTerm] = {
    pt match {
      case PredNot(_) => Set() // TODO: internal part might contain important information (e.g. double negation)
      case PredAnd(a, b) => collectContainedPermissions(a).union(collectContainedPermissions(b))
      case p: PredFieldAcc => Set(p)
      case p: PredImpl => Set(p)
      case p: PredPredAcc => Set(p)
      case PredTrue() => Set()
      case _ => throw new IllegalArgumentException(s"Unable to collect contained permissions from ${pt.getClass.getName}")
    }
  }

  def processsssss(defs: Map[String, PredDef], seq: Sequence): Seq[(Injection, FoldingStep)] = {
    val knowledge = KnowledgeBase(Set())
    val tpt = TransparentPredicateTree(Seq(), Set(), Set())
    val result = processWithVals(defs, seq, knowledge, tpt)
    result._2.foldingStory
  }

  case class PermissionRequirements(fields: Set[FieldAcc], predicates: Set[PredInstance]) {
    def withField(field: FieldAcc): PermissionRequirements = {
      PermissionRequirements(this.fields.union(Set(field)), this.predicates)
    }

    def withPred(pred: PredInstance): PermissionRequirements = {
      PermissionRequirements(this.fields, this.predicates.union(Set(pred)))
    }

    def merge(other: PermissionRequirements): PermissionRequirements = {
      PermissionRequirements(this.fields.union(other.fields), this.predicates.union(other.predicates))
    }

    def substitute(init: VariableInstantiation): PermissionRequirements = {
      PermissionRequirements(
        this.fields.map(f => f.instantiate(init)),
        this.predicates.map(p => p.instantiate(init))
      )
    }
  }

  def getUnfoldingStrategiesForAllRequirements(depth: Int, ts: TermSub, kb: KnowledgeBase, tpt: TransparentPredicateTree, defs: Map[String, PredDef], requirements: PermissionRequirements): Option[FoldingStrategy] = {
    val start: Option[FoldingStrategy] = Some(FoldingStrategy(Seq()))
    val reqs1 = requirements.fields.map(r => (r.pretty(), tpt.findUnfoldingStrategyForDirect(defs, ts, kb, r, depth)))
    val reqs2 = requirements.predicates.map(p => (p.pretty(), tpt.findRefoldingStrategy(defs, ts, kb, p, depth)))
    (reqs1 ++ reqs2).foldLeft(start)((acc, strat) => {
      acc match {
        case Some(lst) => strat._2 match {
          case Some(steps) => Some(lst.merge(steps))
          case None => {
            println(s"no strategy for ${strat._1}")
            None
          }
        }
        case None => None
      }
    })
  }


  def collectRequirements(t: Term): PermissionRequirements = {
    t match {
      case AddTerm(a, b, _) => {
        val reqA = collectRequirements(a)
        val reqB = collectRequirements(b)
        reqA.merge(reqB)
      }
      case BoolTerm(_, _) => PermissionRequirements(Set(), Set())
      case f@FieldAcc(v, _, _) => {
        collectRequirements(v).withField(f)
      }
      case FracPerm(left, right, _) => {
        val reqA = collectRequirements(left)
        val reqB = collectRequirements(right)
        reqA.merge(reqB)
      }
      case IntTerm(_, _) => PermissionRequirements(Set(), Set())
      case NullTerm(_) => PermissionRequirements(Set(), Set())
      case Var(_, _) => PermissionRequirements(Set(), Set())
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract permission requirements from ${t.getClass.getName}")
      }
    }
  }

  def applySteps(location: Injection, defs: Map[String, PredDef], ts: TermSub, tpt: TransparentPredicateTree, strategy: FoldingStrategy): TransparentPredicateTree = {
    strategy.steps.foldLeft(tpt)((t, s) => {
      if (s.unfolding) {
        t.unfold(location, defs, ts, s.pred.substitute(ts))
      }
      else {
        t.fold(location, defs, ts, s.pred.substitute(ts))
      }
    })
  }

  def processWithVals(defs: Map[String, PredDef], seq: Sequence, initKB: KnowledgeBase, predTree: TransparentPredicateTree): (KnowledgeBase, TransparentPredicateTree) = {
    var knowledge = initKB
    var tpt = predTree
    var equi = Seq[Equivalence]()
    var tempVarCounter = 0

    for (elem <- seq.lines) {
//      println("")
//      println("TPT: " + tpt.pretty())
//      println("KB: " + knowledge.pretty())
//      println(s"EQUI: ${equi.map(_.pretty()).mkString(";")}")
//      println("INST: " + elem.pretty())
      elem match {
        case AssumeLine(pred, know) => {
          val permissions = collectContainedPermissions(pred)
          permissions.foreach({
            case PredPredAcc(pi) => tpt = tpt.inhale(pi)
            case PredFieldAcc(fa) => tpt = tpt.inhale(fa)
            // TODO: implement assuming implication
          })
          knowledge = knowledge.extend(know)
        }
        case NonDetBranch(loc, first, second) => {
          val resultFirst = processWithVals(defs, Sequence(Seq(first)), knowledge, tpt)
          val resultSecond = processWithVals(defs, Sequence(Seq(second)), knowledge, tpt)

          println(">>>>>")
          println("TPT 1: " + resultFirst._2.pretty())
          println("KB 1: " + resultFirst._1.pretty())

          println("TPT 2: " + resultSecond._2.pretty())
          println("KB 2: " + resultSecond._1.pretty())
          println(">>>>>")
          // TODO:
          //  unrestricted access to permissions that both sides have
          //  evening procedure that will fold the field permissions of the respected sides to more combined predicate permissions

          val foldingStory = tpt.foldingStory ++ resultFirst._2.foldingStory ++ resultSecond._2.foldingStory

          // TODO: REWORK THIS
          val direct = resultFirst._2.direct.intersect(resultSecond._2.direct)
          val folded = resultFirst._2.folded.intersect(resultSecond._2.folded)

          tpt = TransparentPredicateTree(foldingStory, direct, folded)
        }
        case VarAssignLine(loc, v, e) => {
          val renaming = Seq(Equivalence(v, Var("$v" + tempVarCounter, v.typ)))
          equi = equi ++ renaming
          tempVarCounter += 1

          // rename the current instance of the variable to a temporary
          val renamingTs = TermSub(renaming.map(v => (v.a, v.b)).toMap)
          knowledge = knowledge.substitute(renamingTs)

          tpt = tpt.substitute(renamingTs)

          val subbedE = e.substitute(renamingTs)

          val req = collectRequirements(subbedE)
          val ts = TermSub(equi.map(v => (v.a, v.b)).toMap)
          val valueStrat = getUnfoldingStrategiesForAllRequirements(searchDepth, ts, knowledge, tpt, defs, req)
          valueStrat match {
            case Some(value) => {
              tpt = applySteps(loc, defs, ts, tpt, value)
            }
            case None => {
              println(s"Unable to find unfolding strategy for: ${elem.pretty()}")
            }
          }
        }
        case seq: Sequence => {

          val result = processWithVals(defs, seq, knowledge, tpt)
          knowledge = result._1
          tpt = result._2
        }
        case InhaleLine(pred) => {
          var current = collectContainedPermissions(pred)
          while (current != Set()) {
            val top = current.toSeq.head
            current = current.diff(Set(top))
            top match {
              case PredImpl(cond, body) => {
                val contained = collectContainedPermissions(body)
                contained.foreach {
                  case PredFieldAcc(fa) => {
//                    println(s"ADDING GUARDED F ACC: ${cond.map(_.pretty()).mkString(" & ")} => ${fa.pretty()}")
                    tpt = tpt.inhale(cond, fa)
                  }
                  case PredPredAcc(pi) => {
//                    println(s"ADDING GUARDED P INST: ${cond.map(_.pretty()).mkString(" & ")} => ${pi.pretty()}")
                    tpt = tpt.inhale(cond, pi)
                  }
                  case p => {
                    throw new IllegalArgumentException(s"Unable to process nested permissions ${p}")
                  }
                }
              }
              case PredFieldAcc(fa) => {
                tpt = tpt.inhale(fa)
                knowledge.extend(collectKnowledgeAboutTerm(fa))
              }
              case PredPredAcc(pi) => {
                tpt = tpt.inhale(pi)

                val predDef = defs(pi.name)
                val vars = VariableInstantiation(predDef.params.zip(pi.values).toMap)
                val facs = predDef.body.instantiate(vars)
                  .direct.map(v => collectKnowledgeAboutTerm(v._2))
                  .foldLeft(Set[Knowledge]())((a, b) => a.union(b))

                knowledge = knowledge.extend(facs)
              }
            }
          }
        }
        case FieldAssignLine(loc, v, e) => {
          val renaming = Seq(Equivalence(v, Var("$v" + tempVarCounter, v.typ)))
          equi = equi ++ renaming
          tempVarCounter += 1

          // rename the current instance of the variable to a temporary
          val renamingTs = TermSub(renaming.map(v => (v.a, v.b)).toMap)
          knowledge = knowledge.substitute(renamingTs)
          // TODO: potentially construct a secondary renaming that will only touch the variables
          // when assigned like: x.value := something then
          //    acc(x.value) is unchanged
          //    acc(x.value.field) becomes acc($v1.field)
          // QUESTION: what happens when something = x
          // TODO: ALSO RENAME THE OLD INSTANCES IN THE EXPR OF THE ASSIGNMENT
          //       -> rename x to vX and have equivalence x = vX by assignment
          tpt = tpt.substitute(renamingTs)

          val subbedE = e.substitute(renamingTs)

          val adjusted = Equivalence(v, subbedE)
          equi = equi ++ Seq(adjusted)
          val adjustingTs = TermSub(Seq((adjusted.a, adjusted.b)).toMap)
          tpt = tpt.substitute(adjustingTs)
          knowledge = knowledge.substitute(adjustingTs)

          val req = collectRequirements(subbedE)
          val ts = TermSub(equi.map(v => (v.a, v.b)).toMap)
          val valueStrat = getUnfoldingStrategiesForAllRequirements(searchDepth, ts, knowledge, tpt, defs, req)
          valueStrat match {
            case Some(value) => {
              tpt = applySteps(loc, defs, ts, tpt, value)
            }
            case None => {
              println(s"Unable to find unfolding strategy for: ${elem.pretty()}")
            }
          }

          val destStrat = tpt.findUnfoldingStrategyForDirect(defs, ts, knowledge, v, searchDepth)
          destStrat match {
            case Some(value) => {
              tpt = applySteps(loc, defs, ts, tpt, value)
            }
            case None => {
              println(s"Unable to find unfolding strategy for: ${elem.pretty()}")
            }
          }
//          println(s"HAVING EQUIVALENCE: ${v} == ${e}")
          //Equivalence(v, e)
        }
        case ExhaleLine(loc, pred) => {
          val ts = TermSub(equi.map(v => (v.a, v.b)).toMap)
          val subbedPred = pred.substitute(ts)
//          println(s"SUBBED PRED: ${subbedPred}")
          var current = collectContainedPermissions(subbedPred)
//          println(s"CONTAINED PERMISSIONS: ${current}")
          while (current != Set()) {
            val top = current.toSeq.head
            current = current.diff(Set(top))
            top match {
              case PredImpl(cond, body) => {
                val allSat = cond.forall(c => knowledge.prove(c) == SAT)
                if (allSat) {
                  current = current.union(collectContainedPermissions(body))
                }
              }
              case PredFieldAcc(fa) => {

                tpt = tpt.exhale(fa)
                // TODO: delete knowledge regarding this stuff
              }
              case PredPredAcc(pi) => {
                tpt.findRefoldingStrategy(defs, ts, knowledge, pi, searchDepth) match {
                  case Some(value) => {
                    tpt = applySteps(loc, defs, ts, tpt, value)
                  }
                  case None => {
                    // TODO: report error / collect errors
                    println(s"Unable to find refolding strategy for ${pi.pretty()}")
                  }
                }
                tpt = tpt.exhale(pi)
                // TODO: delete knowledge regarding this stuff
              }
            }
          }
        }
        case _ => {
          throw new IllegalArgumentException(s"NIM ${elem.getClass.getName}")
        }
      }
    }
    (knowledge, tpt)
  }

  def collectFoldingStoryFor(foldingStory: Seq[(Stmt, FoldingStep)], stmt: Stmt): Seq[FoldingStep] = {
    foldingStory.filter(v => v._1.equals(stmt))
      .map(_._2)
  }

  def termToExp(term: Term): Exp = {
    term match {
      case AddTerm(a, b, _) => Add(termToExp(a), termToExp(b))()
      case BoolTerm(value, _) => if (value) TrueLit()() else FalseLit()()
      case FieldAcc(v, field, typ) => FieldAccess(termToExp(v), Field(field, typ)())()
      case FracPerm(left, right, _) => FractionalPerm(termToExp(left), termToExp(right))()
      case IntTerm(value, _) => IntLit(value)()
      case NullTerm(_) => NullLit()()
      case Var(name, typ) => LocalVar(name, typ)()
      case _ => {
        throw new IllegalArgumentException(s"Unable to convert term ${term.getClass.getName} to exp!")
      }
    }
  }

  def wrapWithFoldingStory(foldingStory: Seq[(Injection, FoldingStep)], stmt: Stmt): Stmt = {
    val story = collectFoldingStoryFor(foldingStory, stmt)
      .map(s => {
        val args = s.pred.values.map(t => termToExp(t))
        val predAcc = PredicateAccess(args, s.pred.name)()
        val pap = PredicateAccessPredicate(predAcc, None)()
        // TODO: extend with permission amount
        if (s.unfolding) Unfold(pap)() else Fold(pap)()
      })

    Seqn(story, Seq())()
  }

  def injectFoldingStory(foldingStory: Seq[(Injection, FoldingStep)], stmt: Stmt): Stmt = {
    stmt match {
      case i: Injection => wrapWithFoldingStory(foldingStory, i)
      case s: Seqn => {
        val injected = s.ss.map(s => injectFoldingStory(foldingStory, s))
        Seqn(injected, s.scopedSeqnDeclarations)(s.pos, s.info, s.errT)
      }
      case s@If(cond, thn, els) => {
        val mappedThn = injectFoldingStory(foldingStory, thn).asInstanceOf[Seqn]
        val mappedEls = injectFoldingStory(foldingStory, els).asInstanceOf[Seqn]
        If(cond, mappedThn, mappedEls)(s.pos, s.info, s.errT)
      }
      // TODO: extend for while stmt
//      case e => {
//        throw new IllegalArgumentException(s"Unable to inject folding story into ${e.getClass.getName}")
//      }
      case s => s
    }
  }

  

  def inferPermissionStory(defs: Map[String, PredDef], method: Method): Method = {
    println(s"METHOD: ${method.name}")
    val mappedBody = method.body.map((methBody: Seqn) => {

      val inhaling = Sequence(method.pres.map(expToPredTerm)
        .map(v => InhaleLine(v)))

      val lastInj = freshInjection()

      val exhaling = Sequence(method.posts.map(expToPredTerm)
        .map(v => ExhaleLine(lastInj, v))
        .reverse)

      val transformRes = transformSeqnToInternalForm(defs, methBody)
      val joined = inhaling.join(transformRes._2).join(exhaling)
      println("::::::::::::: LINES :::::::::::::::::")
      println(joined.pretty(4))
      println(":::::::::::::::::::::::::::::::::::::")
      val foldingStory = processsssss(defs, joined)
//      println("::::::::::::: FOLDING STORY :::::::::::::::::")
//      foldingStory.foreach(e => println(s"${e._1} :> ${if (e._2.unfolding) "unfolding" else "folding"} ${e._2.pred.pretty()}"))
//      println(":::::::::::::::::::::::::::::::::::::::::::::")
      val extendedBody = Seqn(Seq(transformRes._1, lastInj), Seq())()
      val injected = injectFoldingStory(foldingStory, extendedBody)
      println("::::::::::::::::: INJECTED :::::::::::::::::::")
      println(s"${injected.toString()}")
      println("::::::::::::::::::::::::::::::::::::::::::::::")
      injected.asInstanceOf[Seqn]
    })

    Method(
      method.name,
      method.formalArgs,
      method.formalReturns,
      method.pres,
      method.posts,
      mappedBody
    )(method.pos, method.info, method.errT)
  }

  def process(): Option[Program] = {
    val defs = PredDefConstructor.constructPredicateDefs(this.program)

    val translatedMethods = this.program.methods.map(m => inferPermissionStory(defs, m))

    println("================================================================")
    translatedMethods.foreach(m => {
      println(m.toString())
      println("-----")
    })
    println("FINISHED INFERING")
    Some(Program(
      this.program.domains,
      this.program.fields,
      this.program.functions,
      this.program.predicates,
      translatedMethods,
      this.program.extensions
    )(this.program.pos, this.program.info, this.program.errT))
  }
}
