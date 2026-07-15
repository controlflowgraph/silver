package viper.silver.inference.v2

import viper.silver.ast._
import viper.silver.inference.v2.ast._
import viper.silver.inference.v2.knowledge.Knowledge.collectKnowledgeAboutTerm
import viper.silver.inference.v2.knowledge.{Equivalence, IsNonNull, IsNull, Knowledge, KnowledgeBase, SAT}

case class Infer(program: Program) {

  val searchDepth = 10

  def expToTerm(exp: Exp): Term = {
    exp match {
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

  def transformSeqnToInternalForm(defs: Map[String, PredDef], seq: Seqn): Sequence = {
    Sequence(seq.ss.map(s => translateStmtToInternalForm(defs, s)))
  }


  def translateStmtToInternalForm(defs: Map[String, PredDef], stmt: Stmt): Line = {
    stmt match {
      case NewStmt(lhs, fields) => {

        // TODO: rename the current target to some temporary variable value (the knowledge relating that)

        // inhaling access to the new location
        val mappedVar = expToTerm(lhs)
        val mapped = fields.map(f => FieldAcc(mappedVar, f.name, f.typ))
          .map(f => PredFieldAcc(f))
          .reduceOption[PredTerm]((a, b) => PredAnd(a, b))
          .getOrElse(PredTrue())

        InhaleLine(mapped)
      }
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) => VarAssignLine(
          Var(lhs.name, lhs.typ),
          expToTerm(rhs)
        )
        case FieldAssign(lhs, rhs) => FieldAssignLine(
          FieldAcc(expToTerm(lhs.rcv), lhs.field.name, lhs.typ),
          expToTerm(rhs)
        )
      }
      case MethodCall(methodName, args, targets) => {
//        MethodCallLine(
//          targets.map(t => Var(t.name, t.typ)),
//          methodName,
//          args.map(a => expToTerm(a))
//        )
        // TODO: remove knowledge about the passed arguments

        val meth = this.program.methods.find(m => m.name.equals(methodName))
          .get

        val argRepl = meth.formalArgs.map(d => Var(d.name, d.typ)).zip(args.map(expToTerm))

        val exhales = meth.pres.map(p => expToPredTerm(p))
          .map(t => t.substitute(TermSub(argRepl.toMap)))
          .map(v => InhaleLine(v))

        val retRepl = meth.formalReturns.map(v => Var(v.name, v.typ)).zip(targets.map(v => Var(v.name, v.typ)))

        val inhales = meth.posts.map(p => expToPredTerm(p))
          .map(t => t.substitute(TermSub((argRepl ++ retRepl).toMap)))
          .map(v => InhaleLine(v))

        Sequence(exhales ++ inhales)
      }
      case Exhale(exp) => ExhaleLine(expToPredTerm(exp))
      case Inhale(exp) => InhaleLine(expToPredTerm(exp))
      case Assert(exp) => AssertLine(expToPredTerm(exp))
      case Assume(exp) => AssumeLine(expToPredTerm(exp))
      case Fold(acc) => {
        val inst = instantiatePredicateFolding(defs, acc)
        val body = inst._2
        val folded = inst._1

        Sequence(Seq(
          ExhaleLine(body),
          InhaleLine(folded)
        ))
      }
      case Unfold(acc) => {
        val inst = instantiatePredicateFolding(defs, acc)
        val body = inst._2
        val folded = inst._1


        Sequence(Seq(
          ExhaleLine(folded),
          InhaleLine(body)
        ))
      }

      case seq: Seqn => transformSeqnToInternalForm(defs, seq)
      case If(cond, thn, els) => {

        val translatedCondition = expToPredTerm(cond)
        NonDetBranch(
          transformSeqnToInternalForm(defs, thn).prepend(AssumeLine(translatedCondition)),
          transformSeqnToInternalForm(defs, els).prepend(AssumeLine(PredNot(translatedCondition))),
        )
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
      case PredAnd(a, b) => collectContainedPermissions(a).union(collectContainedPermissions(b))
      case p: PredFieldAcc => Set(p)
      case p: PredImpl => Set(p)
      case p: PredPredAcc => Set(p)
      case PredTrue() => Set()
      case _ => throw new IllegalArgumentException(s"Unable to collect contained permissions from ${pt.getClass.getName}")
    }
  }

  def processsssss(defs: Map[String, PredDef], seq: Sequence): Unit = {
    val knowledge = KnowledgeBase(Set())
    val tpt = TransparentPredicateTree(Set(), Set())
    processWithVals(defs, seq, knowledge, tpt)
  }

  case class PermissionRequirements(fields: Set[FieldAcc], predicates: Set[PredInstance]) {
    def withField(field: FieldAcc) : PermissionRequirements = {
      PermissionRequirements(this.fields.union(Set(field)), this.predicates)
    }

    def withPred(pred: PredInstance) : PermissionRequirements = {
      PermissionRequirements(this.fields, this.predicates.union(Set(pred)))
    }

    def merge(other: PermissionRequirements) : PermissionRequirements = {
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
    println(s"reqs1: ${reqs1}")
    println(s"reqs2: ${reqs2}")
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



  def collectRequirements(t: Term) : PermissionRequirements = {
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
      case FracPerm(left, right, _) =>{
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

  def applySteps(defs: Map[String, PredDef], ts: TermSub, tpt: TransparentPredicateTree, strategy: FoldingStrategy) : TransparentPredicateTree = {
    strategy.steps.foldLeft(tpt)((t, s) => {
      if (s.unfolding) {
        t.unfold(defs, ts, s.pred.substitute(ts))
      }
      else {
        t.fold(defs, ts, s.pred.substitute(ts))
      }
    })
  }

  def processWithVals(defs: Map[String, PredDef], seq: Sequence, initKB: KnowledgeBase, predTree: TransparentPredicateTree): (KnowledgeBase, TransparentPredicateTree) = {
    var knowledge = initKB
    var tpt = predTree
    var equi = Seq[Equivalence]()
    var tempVarCounter = 0

    for (elem <- seq.lines) {
      println("")
      println("TPT: " + tpt.pretty())
      println("KB: " + knowledge.pretty())
      println(s"EQUI: ${equi.map(_.pretty()).mkString(";")}")
      println("INST: " + elem.pretty())
      elem match {
        case VarAssignLine(v, e) => {
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
              tpt = applySteps(defs, ts, tpt, value)
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
          println(s"INHALING ALL: ${current.map(_.pretty()).mkString(";;")}")
          while (current != Set()) {
            val top = current.toSeq.head
            println(s"TOP: ${top.pretty()}")
            current = current.diff(Set(top))
            top match {
              case PredImpl(cond, body) => {
                val contained = collectContainedPermissions(body)
                contained.foreach {
                  case PredFieldAcc(fa) => {
                    println(s"ADDING GUARDED F ACC: ${cond.map(_.pretty()).mkString(" & ")} => ${fa.pretty()}")
                    tpt = tpt.inhale(cond, fa)
                  }
                  case PredPredAcc(pi) => {
                    println(s"ADDING GUARDED P INST: ${cond.map(_.pretty()).mkString(" & ")} => ${pi.pretty()}")
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
        case FieldAssignLine(v, e) => {
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
              tpt = applySteps(defs, ts, tpt, value)
            }
            case None => {
              println(s"Unable to find unfolding strategy for: ${elem.pretty()}")
            }
          }

          val destStrat = tpt.findUnfoldingStrategyForDirect(defs, ts, knowledge, v, searchDepth)
          destStrat match {
            case Some(value) => {
              tpt = applySteps(defs, ts, tpt, value)
            }
            case None => {
              println(s"Unable to find unfolding strategy for: ${elem.pretty()}")
            }
          }
          println(s"HAVING EQUIVALENCE: ${v} == ${e}")
          //Equivalence(v, e)
        }
        case ExhaleLine(pred) => {
          val ts = TermSub(equi.map(v => (v.a, v.b)).toMap)
          val subbedPred = pred.substitute(ts)
          println(s"SUBBED PRED: ${subbedPred}")
          var current = collectContainedPermissions(subbedPred)
          println(s"CONTAINED PERMISSIONS: ${current}")
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
                    tpt = applySteps(defs, ts, tpt, value)
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

  def translateMethodToInternalForm(defs: Map[String, PredDef], method: Method): Unit = {
    println(s"METHOD: ${method.name}")
    val mappedBody = method.body.map(v => {
      val inhaling = Sequence(method.pres.map(expToPredTerm)
        .map(v => InhaleLine(v)))
      val exhaling = Sequence(method.posts.map(expToPredTerm)
        .map(v => ExhaleLine(v))
        .reverse)

      val body = transformSeqnToInternalForm(defs, v)
      val joined = inhaling.join(body).join(exhaling)
      println("::::::::::::: LINES :::::::::::::::::")
      println(joined.pretty(4))
      println(":::::::::::::::::::::::::::::::::::::")
      processsssss(defs, joined)
      joined
    })
  }

  def process(): Option[Program] = {
    val defs = PredDefConstructor.constructPredicateDefs(this.program)

    val translatedMethods = this.program.methods.map(m => translateMethodToInternalForm(defs, m))
    println("FINISHED INFERING")
    None
  }
}
