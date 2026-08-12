package viper.silver.inference.v2

import viper.silver.ast._
import viper.silver.inference.v2.ast._
import viper.silver.inference.v2.knowledge.Knowledge.collectKnowledgeAboutTerm
import viper.silver.inference.v2.knowledge.{Equivalence, IsNonNull, IsNull, Knowledge, KnowledgeBase, SAT}

import java.util.Objects
import scala.collection.immutable.HashMap
import scala.collection.mutable

case class Infer(program: Program) {

  val searchDepth = 10

  def expToTerm(exp: Exp): Term = {
    exp match {
      case Add(a, b) => AddTerm(expToTerm(a), expToTerm(b), exp.typ)
      case Sub(a, b) => SubTerm(expToTerm(a), expToTerm(b), exp.typ)
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
      case _: EqCmp => PredTrue()
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

  def transformSeqnToInternalForm(defs: Map[String, PredDef], seq: Seqn, inj: Option[Injection]): (Seqn, Sequence) = {
    val transformed: Seq[(Stmt, Line)] = seq.ss.map(s => translateStmtToInternalForm(defs, s))
    val injection = inj match {
      case Some(value) => Seq(value)
      case None => Seq()
    }
    (Seqn(transformed.map(_._1) ++ injection, seq.scopedSeqnDeclarations)(), Sequence(transformed.map(_._2)))
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

        val reqs = this.program.inferInfo.typeAnnotations(methodName)
        val argNames = this.program.methods.filter(m => m.name.equals(methodName)).head.formalArgs.map(f => f.name)
        val paramedExhaling: Seq[ExhaleLine] = reqs._1.zip(argNames).flatMap(t => t._1 match {
          case dt: DatatypeType => {
            val name = encodeTypeAsString(dt)
            val term = PredImpl(Set(IsNonNull(Var(t._2, Ref))), PredPredAcc(PredInstance(name, Seq(Var(t._2, Ref)))))
            Seq(ExhaleLine(inj, term.substitute(TermSub((argRepl ++ retRepl).toMap))))
          }
          case _ => Seq()
        })

        val retNames = this.program.methods.filter(m => m.name.equals(methodName)).head.formalReturns.map(f => f.name)
        val paramedInhaling = reqs._2.zip(retNames).flatMap(t => t._1 match {
          case dt: DatatypeType => {
            val name = encodeTypeAsString(dt)
            val term = PredPredAcc(PredInstance(name, Seq(Var(t._2, Ref))))
            Seq(InhaleLine(term.substitute(TermSub(argRepl.toMap))))
          }
          case _ => Seq()
        })

        val line = Sequence(((paramedExhaling ++ exhales).reverse) ++ paramedInhaling ++ inhales)
        println(s"LINE FOR METH CALL: ${line}")
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

      case seq: Seqn => transformSeqnToInternalForm(defs, seq, None)
      case i@If(cond, thn, els) => {

        // TODO: potentially split the condition into pred term and knowledge set
        val translatedCondition = expToPredTerm(cond)
        val knowledge = Knowledge.conditionToKnowledgeSet(cond)
        val inj = freshInjection()
        val firstInj = freshInjection()
        val secondInj = freshInjection()

        val thnTrans = transformSeqnToInternalForm(defs, thn, Some(firstInj))
        val elsTrans = transformSeqnToInternalForm(defs, els, Some(secondInj))

        val line = Branching(
          inj,
          cond,
          thnTrans._2.prepend(AssumeLine(PredRewriter.simplify(translatedCondition), knowledge)),
          elsTrans._2.prepend(AssumeLine(PredRewriter.simplify(PredNot(translatedCondition)), knowledge.map(_.negate()))),
          firstInj,
          secondInj
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
      case PredFalse() => Set()
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

  def collectRequirements(t: Exp): PermissionRequirements = {
    t match {
      case FieldAccess(rcv, field) => collectRequirements(rcv).withField(FieldAcc(expToTerm(rcv), field.name, field.typ))
      case exp: BinExp => exp.args.map(a => collectRequirements(a))
        .foldLeft(PermissionRequirements(Set(), Set()))((a, b) => a.merge(b))
      case lv: LocalVar => PermissionRequirements(Set(), Set())
      case _ => PermissionRequirements(Set(), Set())
    }
  }

  def collectRequirements(t: Term): PermissionRequirements = {
    t match {
      case AddTerm(a, b, _) => {
        val reqA = collectRequirements(a)
        val reqB = collectRequirements(b)
        reqA.merge(reqB)
      }
      case SubTerm(a, b, _) => {
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
        t.fold(location, defs, ts, s.pred.substitute(ts), Set())
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
        case Branching(loc, cond, first, second, finj, sinj) => {
          val requirements = collectRequirements(cond)
          val ts = TermSub(equi.map(v => (v.a, v.b)).toMap)
          println("=========-------------")
          println(requirements.fields)
          println(requirements.predicates)
          val afterFieldsTpt = requirements.fields.foldLeft(tpt)((t, f) => {
            val optStrat = t.findUnfoldingStrategyForDirect(defs, ts, knowledge, f, searchDepth)
            optStrat match {
              case Some(value) => {
                println(s"UNFOLDING STORY: ${value}")
                println(s"TS: ${ts}")
                println(t.foldingStory)
                println(s"BEFORE UNFOLDING (FIELD): ${t.pretty()}")
                val res = applySteps(loc, defs, ts, t, value)
                println(s"AFTER UNFOLDING (FIELD): ${res.pretty()}")
                println(res.foldingStory)
                res
              }
              case None => t
            }
          })
          println("AFTER FIELDS TPT")
          println(afterFieldsTpt.pretty())
          val afterPredsTpt = requirements.predicates.foldLeft(afterFieldsTpt)((t, f) => t.findPredInstanceUnfoldingStrategy(defs, knowledge, f, searchDepth)
            .map(s => {
              println(s"BEFORE UNFOLDING: ${t.pretty()}")
              val res = applySteps(loc, defs, ts, t, s)
              println(s"AFTER UNFOLDING: ${res.pretty()}")
              res
            }).getOrElse(t))
          println("AFTER PREDS TPT")
          println(afterPredsTpt.pretty())
          val resultFirst = processWithVals(defs, Sequence(Seq(first)), knowledge, afterPredsTpt)
          val resultSecond = processWithVals(defs, Sequence(Seq(second)), knowledge, afterPredsTpt)

          println(">>>>>")
          println("TPT 1: " + resultFirst._2.pretty())
          println("KB 1: " + resultFirst._1.pretty())

          println("TPT 2: " + resultSecond._2.pretty())
          println("KB 2: " + resultSecond._1.pretty())
          println(">>>>>")
          // TODO:
          //  unrestricted access to permissions that both sides have
          //  evening procedure that will fold the field permissions of the respected sides to more combined predicate permissions

          println(s"LEFT FROM FIRST: ${resultFirst._2.direct.diff(resultSecond._2.direct)}")
          val foldedLeftFromFirst = resultFirst._2.folded.diff(resultSecond._2.folded)
          println(s"LEFT FROM FIRST: $foldedLeftFromFirst")
          println("")
          println(s"LEFT FROM SECOND: ${resultSecond._2.direct.diff(resultFirst._2.direct)}")
          val foldedLeftFromSecond = resultSecond._2.folded.diff(resultFirst._2.folded)
          println(s"LEFT FROM SECOND: $foldedLeftFromSecond")
          val adjustedStpt = foldedLeftFromFirst.foldLeft(resultSecond._2)((stpt, p) => {
            val ts = TermSub(this.program.predicates.filter(a => a.name.equals(p._2.name)).head.formalArgs.zip(p._2.values)
              .map(v => (Var(v._1.name, v._1.typ), v._2))
              .toMap)
            val result = stpt.findRefoldingStrategy(defs, ts, resultSecond._1, p._2, searchDepth)
            result match {
              case Some(value) => {
                println(s"refolding strategy for: ${p} ${value}")
                println(s"KNOWLEDGE FOR THE FIRST: ${p._1}")
                stpt.fold(sinj, defs, ts, p._2, p._1)
              }
              case None => stpt
            }
          })


          // TODO: adjust the knowledge base as well
          val direct = resultFirst._2.direct.intersect(adjustedStpt.direct)
          val folded = resultFirst._2.folded.intersect(adjustedStpt.folded)
          println(s"JOIN OPERATOR: ${direct}  ${folded}")
          val commonStoryLength = afterPredsTpt.foldingStory.length
          val foldingStory = afterPredsTpt.foldingStory ++ resultFirst._2.foldingStory.drop(commonStoryLength) ++ adjustedStpt.foldingStory.drop(commonStoryLength)



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

  def encodeTypeAsString(typ: Type): String = {
    typ match {
      case inType: BuiltInType => inType match {
        case atomicType: AtomicType => atomicType match {
          case Int => "Int"
          case Bool => "Bool"
          case Perm => "Perm"
          case Ref => "Ref"
          case InternalType => "InternalType"
          case Wand => "Wand"
          case BackendType(viperName, _) => viperName
        }
        case collectionType: CollectionType => collectionType match {
          case SeqType(elementType) => s"Seq${encodeTypeListAsString(Seq(elementType))}"
          case SetType(elementType) => s"Set${encodeTypeListAsString(Seq(elementType))}"
          case MultisetType(elementType) => s"Multiset${encodeTypeListAsString(Seq(elementType))}"
        }
        case MapType(keyType, valueType) => s"Map${encodeTypeListAsString(Seq(keyType, valueType))}"
      }
      case extensionType: ExtensionType => ???
      case genericType: GenericType => genericType match {
        case DomainType(domainName, partialTypVarsMap) => domainName // TODO: fix this s"${domainName}${encodeTypeListAsString(getDomain(domainName).typVars.map(v => partialTypVarsMap(v)))}"
        case DatatypeType(datatypeName, partialTypVarsMap) => {
          val args = Seq()
          // TODO: fix the encoding of the types
//          getDatatype(datatypeName)
//            .generics
//            .map(g => TypeVar(g))
//            .map(v => partialTypVarsMap(v))
          val generics = encodeTypeListAsString(args)
          s"${datatypeName}$generics"
        }
      }
      case TypeVar(name) => s"${"$$$$"}_${name}"
      case _ => ???
    }
  }


  def encodeTypeListAsString(typ: Seq[Type]): String = {
    if (typ.isEmpty) ""
    else {
      val joined = typ.map(encodeTypeAsString)
        .reduceOption((a, b) => a + "$$$_" + b)
        .getOrElse("")
      s"${"$$_"}${joined}${"$$$$_"}"
    }
  }


  def inferPermissionStory(defs: Map[String, PredDef], method: Method): Method = {
    println(s"METHOD: ${method.name}")
    val mappedBody = method.body.map((methBody: Seqn) => {

      val reqs = this.program.inferInfo.typeAnnotations(method.name)
      val argNames = method.formalArgs.map(l => l.name)
      val paramedInhaling: Sequence = Sequence(reqs._1.zip(argNames).flatMap(t => t._1 match {
        case dt: DatatypeType => {
          val name = encodeTypeAsString(dt)
          val term = PredImpl(Set(IsNonNull(Var(t._2, Ref))), PredPredAcc(PredInstance(name, Seq(Var(t._2, Ref)))))
          Seq(InhaleLine(term))
        }
        case _ => Seq()
      }))

      val inhaling = Sequence(method.pres.map(expToPredTerm)
        .map(v => InhaleLine(v)))

      val lastInj = freshInjection()


      val retNames = method.formalReturns.map(l => l.name)
      val paramedExhaling = reqs._2.zip(retNames).flatMap(t => t._1 match {
        case dt: DatatypeType => {
          val name = encodeTypeAsString(dt)
          val term = PredImpl(Set(IsNonNull(Var(t._2, Ref))), PredPredAcc(PredInstance(name, Seq(Var(t._2, Ref)))))
          Seq(ExhaleLine(lastInj, term))
        }
        case _ => Seq()
      })

      val exhaling = method.posts.map(expToPredTerm)
        .map(v => ExhaleLine(lastInj, v))

      val transformRes = transformSeqnToInternalForm(defs, methBody, None)
      val joined = paramedInhaling.join(inhaling).join(transformRes._2).join(Sequence((paramedExhaling ++ exhaling).reverse))
      println("::::::::::::: LINES :::::::::::::::::")
      println(joined.pretty(4))
      println(":::::::::::::::::::::::::::::::::::::")
      println(transformRes._1)
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

  def flattenSeqStructure(seq: Sequence): Sequence = {
    var queue: Seq[Line] = seq.lines
    var flattened: Seq[Line] = Seq()
    while (queue.nonEmpty) {
      val head: Line = queue.head
      queue = queue.tail
      head match {
        case Sequence(sub) => queue = sub ++ queue
        case e => flattened = flattened ++ Seq(flattenLineStructure(e))
      }
    }
    Sequence(flattened)
  }

  def flattenLineStructure(line: Line): Line = {
    line match {
      case Branching(location, cond, first, second, finj, sinj) =>
        val firstFlattened = flattenLineStructure(first)
        val secondFlattened = flattenLineStructure(second)
        Branching(location, cond, firstFlattened, secondFlattened, finj, sinj)
      case s: Sequence => flattenSeqStructure(s)
      case e => e
    }
  }

  def process(): Option[Program] = {

    println("================================================================")
    println("================================================================")
    println("================================================================")
    computeTraversals(this.program.predicates)

    val mutating = computeMethodMutation(this.program.methods)

    this.program.methods
      .filter(m => !mutating.contains(m.name))
      .map(n => (n.name, computeFunctionalRepresentation(n)))
      .foreach(p => {
        println(s"METHOD ${p._1} MAPPED TO FUNCTION:")
        println(p._2)
        val mapped = p._2.flatMap(b => b.body.map(a => computeFunctionBaseCases(a, Set(b.name))))
        println(s"Base cases: ${mapped}")
      })

    println("================================================================")
    this.program.methods.foreach(n => {
      println(s"METHOD OUTLINE COMPUTE: ${n.name}")
      println(n)
      println(" ")
      computeOutline(n);
    })


    println("================================================================")

    this.program.inferInfo.typeAnnotations.foreach(v => {
      println(s"${v._1}: ${v._2._1} => ${v._2._2}")
    })

    println("================================================================")
    println("================================================================")
    println("================================================================")

    val defs = PredDefConstructor.constructPredicateDefs(this.program)

    val translatedMethods = this.program.methods.map(m => inferPermissionStory(defs, m))

    //    println("================================================================")
    //    translatedMethods.foreach(m => {
    //      println(m.toString())
    //      println("-----")
    //    })
    //    println("FINISHED INFERRING")

    Some(Program(
      this.program.domains,
      this.program.fields,
      this.program.functions,
      this.program.predicates,
      translatedMethods,
      this.program.extensions,
      this.program.inferInfo,
    )(this.program.pos, this.program.info, this.program.errT))

    None
  }

  def checkContainedRecursiveInstance(name: String, exp: Exp): Set[FieldAccess] = {
    exp match {
      case predicate: AccessPredicate => predicate match {
        //        case MagicWand(left, right) =>
        case FieldAccessPredicate(loc, permExp) => Set()
        case PredicateAccessPredicate(loc, permExp) => {
          if (name == loc.predicateName) {
            // TODO: assumes single argument predicate -> requires main traversal argument
            loc.args.toSet.filter(ex => ex.isInstanceOf[FieldAccess])
              .map(ex => ex.asInstanceOf[FieldAccess])
          } else {
            Set()
          }
        }
      }
        // TODO: implication dictates conditionals for generated traversal/extraction function
      case Implies(left, right) => checkContainedRecursiveInstance(name, right)
      case LeCmp(a, b) => Set()
      case access: LocationAccess => Set()
      case Unfolding(acc, body) => checkContainedRecursiveInstance(name, body)
      case localVar: AbstractLocalVar => localVar match {
        case LocalVar(name, typ) => Set()
        case Result(typ) => Set()
        case LocalVarWithVersion(name, typ) => Set()
      }
      case exp: SeqExp => Set()
      case exp: SetExp => Set()
      case exp: MultisetExp => Set()
      case exp: MapExp => Set()
      case literal: Literal => Set()
      case And(a, b) => {
        val traversalA = checkContainedRecursiveInstance(name, a)
        val traversalB = checkContainedRecursiveInstance(name, b)
        traversalA.union(traversalB)
      }
    }
  }

  def hasTraversal(pred: Predicate): Boolean = {
    pred.body.exists(b => {
      checkContainedRecursiveInstance(pred.name, b).nonEmpty
    })
  }

  def computeTraversals(preds: Seq[Predicate]): Unit = {
    preds.filter(pred => hasTraversal(pred))
      .foreach(pred => {
        val result = pred.body.map(b => checkContainedRecursiveInstance(pred.name, b)).getOrElse(Set())
        println(s"${pred.name} has full traversal: ${result}")
      })
  }

  def computeMethodDependencies(stmt: Stmt): Set[String] = {
    stmt match {
      case NewStmt(lhs, fields) => Set()
      case assign: AbstractAssign => Set()
      case MethodCall(methodName, args, targets) => Set(methodName)
      case Exhale(exp) => Set()
      case Inhale(exp) => Set()
      case Assert(exp) => Set()
      case Assume(exp) => Set()
      case Fold(acc) => Set()
      case Unfold(acc) => Set()
      case Package(wand, proofScript) => Set()
      case Apply(exp) => Set()
      case Seqn(ss, scopedSeqnDeclarations) => ss.flatMap(computeMethodDependencies).toSet
      case If(cond, thn, els) => {
        val a = computeMethodDependencies(thn)
        val b = computeMethodDependencies(els)
        a.union(b)
      }
      case Injection(id) => Set()
      case While(cond, invs, body) => computeMethodDependencies(body)
      case Label(name, invs) => Set()
      case Goto(target) => Set()
      case LocalVarDeclStmt(decl) => Set()
      case Quasihavoc(lhs, exp) => Set()
      case Quasihavocall(vars, lhs, exp) => Set()
    }
  }

  /**
   * Computes whether the method mutates state.
   * This is done by checking if the method contains a field assignment.
   * Local objects are included and not tracked separately.
   *
   * TODO: refine the tracking to reflect local variables better
   */
  def computeMutationState(stmt: Stmt): Boolean = {
    stmt match {
      case NewStmt(lhs, fields) => false
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) => false
        case FieldAssign(lhs, rhs) => true
      }
      case MethodCall(methodName, args, targets) => false
      case Exhale(exp) => false
      case Inhale(exp) => false
      case Assert(exp) => false
      case Assume(exp) => false
      case Fold(acc) => false
      case Unfold(acc) => false
      case Package(wand, proofScript) => false
      case Apply(exp) => false
      case Seqn(ss, scopedSeqnDeclarations) => ss.exists(computeMutationState)
      case If(cond, thn, els) => {
        val a = computeMutationState(thn)
        val b = computeMutationState(els)
        a || b
      }
      case Injection(id) => false
      case While(cond, invs, body) => computeMutationState(body)
      case Label(name, invs) => false
      case Goto(target) => false
      case LocalVarDeclStmt(decl) => false
      case Quasihavoc(lhs, exp) => false
      case Quasihavocall(vars, lhs, exp) => false
    }
  }

  def computeMethodDependencies(method: Method): Set[String] = {
    method.body.map(computeMethodDependencies).getOrElse(Set())
  }

  def fixpoint[T](init: T, f: T => T): T = {
    val applied = f(init)
    if (init.equals(applied)) {
      init
    }
    else {
      fixpoint(applied, f)
    }
  }

  def computeMethodMutation(methods: Seq[Method]): Set[String] = {
    val current = methods.map(m => (m.name, computeMethodDependencies(m)))
      .toMap

    val mutatingMethods = methods.filter(m => m.body.exists(computeMutationState))
      .map(m => m.name)
      .toSet
    println("mutating before:")
    mutatingMethods.foreach(a => println(s"\t${a}"))

    val fp = fixpoint[Set[String]](
      mutatingMethods,
      state => current.filter(e => state.contains(e._1) || e._2.exists(d => state.contains(d))).keySet)


    println("")
    println("mutating after:")
    fp.foreach(a => println(s"\t${a}"))
    fp
  }

  def computeExprRep(stmt: Stmt, resultVariable: String, recursive: String): Option[Exp] = {
    stmt match {
      case NewStmt(lhs, fields) => None
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) =>
          if (lhs.name.equals(resultVariable))
            Some(rhs)
          else None
        case FieldAssign(lhs, rhs) => None
      }
      case c@MethodCall(methodName, args, targets) =>
        if (methodName.equals(recursive))
          Some(FuncApp("Func$" + recursive, args)(c.pos, c.info, targets.head.typ, c.errT))
        else None
      case Exhale(exp) => None
      case Inhale(exp) => None
      case Assert(exp) => None
      case Assume(exp) => None
        // TODO: maybe this part can be ignored instead of producing none result when doing the functionalization
      case Fold(acc) => None
      case Unfold(acc) => None
      case Package(wand, proofScript) => None
      case Apply(exp) => None
      case Seqn(ss, scopedSeqnDeclarations) => {
        if (ss.isEmpty) {
          None
        }
        else if (ss.length == 1) {
          computeExprRep(ss.last, resultVariable, recursive)
        }
        else {
          // last statement in the sequence must be convertible
          // all previous statements are assumed to be local assignments
          // they are translated to let bindings
          val prev = ss.dropRight(1)
          val last: Option[Exp] = computeExprRep(prev.last, resultVariable, recursive)
          prev.foldRight(last)((stmt, result) => result.flatMap(
            m => {
              stmt match {
                case l@LocalVarAssign(lhs, rhs) => {
                  Some(Let(LocalVarDecl(lhs.name, lhs.typ)(lhs.pos, lhs.info, lhs.errT),
                    rhs,
                    m
                  )(l.pos, l.info, l.errT))
                }
                  // case Seqn(ss, scopedSeqnDeclarations) => TODO: allow nesting of sequences although this might not be relevant
                  // case If(cond, thn, els) => TODO: potentially allow this if there is a usecase / valid mapping
                case _ => None
              }
            }
          ))
        }
      }
      case i@If(cond, thn, els) => {
        val expA = computeExprRep(thn, resultVariable, recursive)
        val expB = computeExprRep(els, resultVariable, recursive)
        (expA, expB) match {
          case (Some(a), Some(b)) => Some(CondExp(cond, a, b)(i.pos, i.info, i.errT))
          case _ => None
        }
      }
      case Injection(id) => None
      case While(cond, invs, body) => None
      case Label(name, invs) => None
      case Goto(target) => None
      case LocalVarDeclStmt(decl) => None // TODO: check if this comes up and needs to be handled gracefully
      case Quasihavoc(lhs, exp) => None
      case Quasihavocall(vars, lhs, exp) => None
      case stmt: ExtensionStmt => None
    }
  }

  def containsRecursiveFunctionCall(exp: Exp, func: Set[String]): Boolean = {
    // TODO: fix mutually recursive functions
    exp match {
      case predicate: AccessPredicate => predicate match {
        case MagicWand(left, right) => containsRecursiveFunctionCall(left, func) || containsRecursiveFunctionCall(right, func)
        case FieldAccessPredicate(loc, permExp) => containsRecursiveFunctionCall(loc, func) || permExp.exists(p => containsRecursiveFunctionCall(p, func))
        case PredicateAccessPredicate(loc, permExp) => containsRecursiveFunctionCall(loc, func) || permExp.exists(p => containsRecursiveFunctionCall(p, func))
      }
      case InhaleExhaleExp(in, ex) => containsRecursiveFunctionCall(in, func) || containsRecursiveFunctionCall(ex, func)
      case exp: PermExp => false // TODO: fix if perm exp could have rec func call
      case access: LocationAccess => access match {
        case FieldAccess(rcv, field) => containsRecursiveFunctionCall(rcv, func)
        case PredicateAccess(args, predicateName) => args.exists(a => containsRecursiveFunctionCall(a, func))
      }
      case CondExp(cond, thn, els) => containsRecursiveFunctionCall(cond, func) || containsRecursiveFunctionCall(thn, func) || containsRecursiveFunctionCall(els, func)
      case Unfolding(acc, body) => containsRecursiveFunctionCall(body, func)
      case Applying(wand, body) => containsRecursiveFunctionCall(body, func)
      case Asserting(a, body) => containsRecursiveFunctionCall(body, func)
      case Let(variable, exp, body) => containsRecursiveFunctionCall(exp, func) || containsRecursiveFunctionCall(body, func)
      case exp: QuantifiedExp => exp match {
        case Forall(variables, triggers, exp) => containsRecursiveFunctionCall(exp, func)
        case Exists(variables, triggers, exp) => containsRecursiveFunctionCall(exp, func)
        case ForPerm(variables, resource, body) => containsRecursiveFunctionCall(body, func)
      }
      case ForPerm(variables, resource, body) => containsRecursiveFunctionCall(body, func)
      case localVar: AbstractLocalVar => localVar match {
        case LocalVar(name, typ) => false
        case Result(typ) => false
        case LocalVarWithVersion(name, typ) => false
      }
      case exp: SeqExp => exp match {
        case EmptySeq(elemTyp) => false
        case ExplicitSeq(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
        case RangeSeq(low, high) => containsRecursiveFunctionCall(low, func) || containsRecursiveFunctionCall(high, func)
        case SeqAppend(left, right) => containsRecursiveFunctionCall(left, func) || containsRecursiveFunctionCall(right, func)
        case SeqIndex(s, idx) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(idx, func)
        case SeqTake(s, n) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(n, func)
        case SeqDrop(s, n) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(n, func)
        case SeqContains(elem, s) => containsRecursiveFunctionCall(elem, func) || containsRecursiveFunctionCall(s, func)
        case SeqUpdate(s, idx, elem) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(idx, func) || containsRecursiveFunctionCall(elem, func)
        case SeqLength(s) => containsRecursiveFunctionCall(s, func)
      }
      case exp: SetExp => exp match {
        case exp: AnySetExp => exp match {
          case exp: AnySetUnExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case exp: AnySetBinExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case MapDomain(base) => containsRecursiveFunctionCall(base, func)
          case MapRange(base) => containsRecursiveFunctionCall(base, func)
        }
        case EmptySet(elemTyp) => false
        case ExplicitSet(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
      }
      case exp: MultisetExp => exp match {
        case exp: AnySetExp => exp match {
          case exp: AnySetUnExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case exp: AnySetBinExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case MapDomain(base) => containsRecursiveFunctionCall(base, func)
          case MapRange(base) => containsRecursiveFunctionCall(base, func)
        }
        case EmptyMultiset(elemTyp) => false
        case ExplicitMultiset(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
      }
      case exp: MapExp => exp match {
        case EmptyMap(keyType, valueType) => false
        case ExplicitMap(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
        case Maplet(key, value) => containsRecursiveFunctionCall(key, func) || containsRecursiveFunctionCall(value, func)
        case MapUpdate(base, key, value) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func) || containsRecursiveFunctionCall(value, func)
        case MapLookup(base, key) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func)
        case MapContains(key, base) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func)
        case MapCardinality(base) => containsRecursiveFunctionCall(base, func)
      }
      case literal: Literal => false
      case DomainFuncApp(funcname, args, typVarMap) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
      case app: FuncLikeApp => app match {
        case FuncApp(funcname, args) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
        case app: AbstractDomainFuncApp => app match {
          case DomainFuncApp(funcname, args, typVarMap) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
          case BackendFuncApp(backendFuncName, args) => func.contains(backendFuncName) || args.exists(a => containsRecursiveFunctionCall(a, func))
          case exp: DomainOpExp => exp match {
            case exp: DomainBinExp => containsRecursiveFunctionCall(exp.left, func) || containsRecursiveFunctionCall(exp.right, func)
            case exp: DomainUnExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          }
        }
      }
      case exp: BinExp => exp match {
        case exp: AnySetBinExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
        case cmp: EqualityCmp => cmp.args.exists(a => containsRecursiveFunctionCall(a, func))
      }
      case exp: UnExp => exp match {
        case exp: OldExp => exp match {
          case Old(exp) => containsRecursiveFunctionCall(exp, func)
          case LabelledOld(exp, oldLabel) => containsRecursiveFunctionCall(exp, func)
          case DebugLabelledOld(exp, oldLabel) => containsRecursiveFunctionCall(exp, func)
        }
      }
    }
  }

  def computeFunctionBaseCases(exp: Exp, func: Set[String]): Set[Exp] = {
    if (!containsRecursiveFunctionCall(exp, func))
      Set(exp)
    else
      exp match {
        case access: LocationAccess => access match {
          case FieldAccess(rcv, field) => Set(exp)
          case _ => Set()
        }
          //        case access: ResourceAccess =>
        case CondExp(cond, thn, els) =>
          if (containsRecursiveFunctionCall(cond, func)) Set()
          else computeFunctionBaseCases(thn, func).union(computeFunctionBaseCases(els, func))
        case Let(variable, exp, body) =>
          if (containsRecursiveFunctionCall(exp, func)) Set()
          else computeFunctionBaseCases(body, func)
          //        case exp: QuantifiedExp =>
          //        case ForPerm(variables, resource, body) =>
        case localVar: AbstractLocalVar => Set()
        case exp: SeqExp => Set()
        case exp: SetExp => Set()
        case exp: MultisetExp => Set()
        case exp: MapExp => Set()
        case literal: Literal => Set()
          //        case trigger: PossibleTrigger =>
          //        case trigger: ForbiddenInTrigger =>
        case FuncApp(funcname, args) => Set()
        case exp: BinExp => Set() // TODO: maybe refine this if there is a use for different base cases
        case exp: UnExp => Set() // TODO: maybe refine this if there is a use for different base cases
          //        case lhs: Lhs =>
          //        case exp: ExtensionExp =>
      }
  }

  def computeFunctionalRepresentation(method: Method): Option[Function] = {
    // FIND THE FUNCTIONS THAT RETURN A REF from a field
    //    compute an additional function that returns the amount of permission from that field (if it exists)
    //    ---> then generate the appropriate function
    // THE FUNCTIONS THAT RETURN PRIMITIVE VALUES ARE IRRELEVANT SINCE THEIR VALUE CAN BE COPIED AND HAS NO ACCESS PERMISSIONS

    if (method.formalReturns.length == 1 && method.formalReturns.head.typ.equals(Ref)) {
      val firstReturn = method.formalReturns.head
      val bodyExp = method.body.flatMap(b => computeExprRep(b, firstReturn.name, method.name))
      // in the posts the resulting formal return needs to be replaced with result
      bodyExp.map(b => Function(
        "Func$" + method.name, method.formalArgs,
        firstReturn.typ, method.pres,
        method.posts, Some(b))
      (method.pos, method.info, method.errT))
    }
    else {
      println(s"Method ${method.name} does not have exactly 1 return!")
      None
    }
  }

  trait Requirement {}

  case class MethCallReq(name: String, args: Seq[ObjIdent], res: Seq[ObjIdent], source: String) extends Requirement {

  }

  case class HasField(src: ObjIdent, field: String, obj: ObjIdent, source: String) extends Requirement {

  }

  case class ObjRef(ident: ObjIdent, source: String, fields: Map[String, ObjIdent]) {

  }

  case class ObjIdent(value: String) {
    override def toString: String = s"'${this.value}"
  }

  case class Counter(var value: Int) {
    def next(): Int = {
      val res = this.value;
      this.value += 1;
      res
    }
  }

  case class Structurer(condition: Seq[Exp], drift: Map[ObjIdent, ObjRef], assignment: Map[String, ObjIdent], var tempCounter: Counter, structure: Set[(Seq[Exp], Requirement)]) {

    def this() = this(Seq(), Map(), Map(), Counter(0), Set())

    def addRequirement(req: Requirement): Structurer = {
      Structurer(this.condition, this.drift, this.assignment, this.tempCounter, this.structure.union(Set((this.condition, req))))
    }

    def initParameter(name: String): Structurer = {
      initDecl(name, "$param")
    }


    def initVariable(name: String): Structurer = {
      initDecl(name, "$var$" + name) // this source type should not matter
    }

    def getAssignmentRef(name: String): ObjIdent = {
      this.assignment.getOrElse(name, null)
    }

    def initDecl(name: String, source: String): Structurer = {
      if (this.assignment.contains(name)) {
        this
      }
      else {
        val ident = freshTemp()
        val or = ObjRef(ident, source, Map())
        Structurer(this.condition, this.drift.updated(ident, or), this.assignment.updated(name, ident), this.tempCounter, this.structure)
      }
    }

    def withCond(cond: Exp): Structurer = {
      Structurer(this.condition ++ Seq(cond), this.drift, this.assignment, this.tempCounter, this.structure)
    }

    def resolveVariable(name: String): ObjIdent = {
      this.assignment(name)
    }

    def freshSourceCall(method: String): String = {
      val value = this.tempCounter.next()
      s"call_${method}_${value}" // TODO: fix this with separating via $
    }

    def freshSourceNew(): String = {
      val value = this.tempCounter.next()
      s"new_${value}" // TODO: fix this with separating via $
    }

    def freshTemp(): ObjIdent = {
      val value = this.tempCounter.next()
      ObjIdent(s"t${value}")
    }

    def freshObj(source: String): (ObjIdent, Structurer) = {
      val f = freshTemp()
      val or = ObjRef(f, source, Map())
      (f, Structurer(this.condition, this.drift.updated(f, or), this.assignment, this.tempCounter, this.structure))
    }

    def performAssignment(source: String, fields: Seq[String], value: ObjIdent): Structurer = {
      if (fields.isEmpty) {
        Structurer(this.condition, this.drift, this.assignment.updated(source, value), this.tempCounter, this.structure)
      }
      else {
        var current = this.assignment(source)
        var remFields = fields
        while (remFields.length > 1) {
          current = this.drift(current).fields(remFields.head)
          remFields = remFields.tail
        }
        val oor = this.drift(current)
        val uor = ObjRef(oor.ident, oor.source, oor.fields.updated(remFields.head, value))
        Structurer(this.condition, this.drift.updated(current, uor), this.assignment, this.tempCounter, this.structure)
      }
    }

    def resolveLookup(source: String, fields: Seq[String]): (ObjIdent, Structurer) = {
      var struct: Structurer = this
      var current = this.assignment(source)
      var remFields = fields
      while (remFields.nonEmpty) {
        val res = struct.resolveField(current, remFields.head)
        current = res._1
        struct = res._2

        remFields = remFields.tail
      }

      (current, struct)
    }

    // TODO: introduce a ValRef type that allows the assignment of value terms
    //       these can be recombined and used to construct all the other simple terms


    def resolveField(obj: ObjIdent, field: String): (ObjIdent, Structurer) = {
      val or = this.drift(obj)
      if (!or.fields.contains(field)) {
        val oi = this.freshTemp()
        val created = ObjRef(oi, or.source, Map())
        val updated = ObjRef(or.ident, or.source, or.fields.updated(field, oi))
        var updatedStructure = this.structure.union(Set((this.condition, HasField(obj, field, oi, or.source))))
        (oi, Structurer(this.condition, this.drift.updated(obj, updated).updated(oi, created), this.assignment, this.tempCounter, updatedStructure))
      }
      else {
        (or.fields(field), this)
      }
    }

    def dump(): String = {
      s"----------------\n\tassignment: ${this.assignment}\n\theap:\n${this.drift.values.map(v => "\t\t" + v.toString).mkString("\n")}\n\tinit-struct: \n${this.structure.map(v => "\t\t" + v._1.map(e => e.toString).mkString(" && ") + " =====> " + v._2).mkString("\n")}"
    }
  }

  def extractFieldAssignTarget(fa: FieldAccess): (String, Seq[String]) = {
    val base = fa.rcv match {
      case lv: LocalVar => (lv.name, Seq())
      case ff: FieldAccess => extractFieldAssignTarget(ff)
      case _ => {
        throw new IllegalArgumentException(s"Unexpected nesting of field assignment! ${fa.rcv.getClass.getName}")
      }
    }

    (base._1, base._2 ++ Seq(fa.field.name))
  }

  def computeOutlineExp(structs: Seq[Structurer], exp: Exp): Seq[(ObjIdent, Structurer)] = {
    exp match {
      case lv: LocalVar => structs.map(s => (s.getAssignmentRef(lv.name), s))
      case fa: FieldAccess => computeOutlineExp(structs, fa.rcv).map(v => {
        val res = extractFieldAssignTarget(fa)
        v._2.resolveLookup(res._1, res._2)
      })
      // TODO: introduce PrimRefs to track in the structure
      case lit: Literal => structs.map(s => (null, s))
      case add: Add => add.args.foldLeft(structs)((ss, e) => computeOutlineExp(ss, e).map(v => v._2)).map(a => (null, a))
      case sub: Sub => sub.args.foldLeft(structs)((ss, e) => computeOutlineExp(ss, e).map(v => v._2)).map(a => (null, a))
    }
  }

  def computeOutlineStmt(structs: Seq[Structurer], stmt: Stmt): Seq[Structurer] = {
    stmt match {
      case NewStmt(lhs, fields) => {
        structs.map(s => s.initVariable(lhs.name))
          .map(s => {
            val t = s.freshObj(s.freshSourceNew())
            t._2.performAssignment(lhs.name, Seq(), t._1)
          })
      }
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) => {
          val res = computeOutlineExp(structs, rhs)
          res.map(r => r._2.performAssignment(lhs.name, Seq(), r._1))
        }
        case FieldAssign(lhs, rhs) => {
          val base = extractFieldAssignTarget(lhs)
          val res = computeOutlineExp(structs, rhs)
          res.map(r => r._2.performAssignment(base._1, base._2, r._1))
        }
      }
      case MethodCall(methodName, args, targets) => {

        val arged = args.foldLeft(structs.map(s => (s, Seq[ObjIdent]())))((ss, a) => {
          ss.flatMap(s => {
              computeOutlineExp(Seq(s._1), a)
                .map(v => (v._2, s._2 ++ Seq(v._1)))
            })
        })
        arged.flatMap(e => {
          val strc = e._1
          val ags = e._2
          val callSrc = strc.freshSourceCall(methodName)
          val targetResult = targets.foldLeft(Seq((strc, Seq[ObjIdent]())))((arr, b) => arr.map(agg => {
              if(b.typ.equals(Ref)) {
                val freshed = agg._1.freshObj(callSrc)
                val result = freshed._2.performAssignment(b.name, Seq(), freshed._1)
                (result, agg._2 ++ Seq(freshed._1))
              }
            else{
              (agg._1, agg._2 ++ Seq[ObjIdent](null))
            }
            }))

          targetResult.map(vvv => {
            vvv._1.addRequirement(MethCallReq(methodName, ags, vvv._2, callSrc))
          })
        })
      }
      case Exhale(exp) => computeOutlineExp(structs, exp).map(v => v._2)
      case Inhale(exp) => computeOutlineExp(structs, exp).map(v => v._2)
      case Assert(exp) => computeOutlineExp(structs, exp).map(v => v._2)
      case Assume(exp) => computeOutlineExp(structs, exp).map(v => v._2)
      case Fold(acc) => ???
      case Unfold(acc) => ???
      case seqn@Seqn(ss, scopedSeqnDeclarations) => computeOutlineSeqn(structs, seqn)
      case If(cond, thn, els) => {
        val branchA = computeOutlineStmt(structs.map(s => s.withCond(cond)), thn)
        val branchB = computeOutlineStmt(structs.map(s => s.withCond(Not(cond)())), els)
        branchA ++ branchB
      }
    }
  }


  def computeOutlineSeqn(structs: Seq[Structurer], seqn: Seqn): Seq[Structurer] = {
    seqn.ss.foldLeft(structs)((str, s) => {
      computeOutlineStmt(str, s)
    })
  }

  def computeOutline(method: Method): Unit = {
    // for each function start with empty pres and empty posts
    // iteratively go through each function.
    //    collect the requirements from the call sites of the function (aka usages)
    // pass through all statements with the new post conditions
    // --> condense to some abstracted representation of what is required (e.g. read/write difference -> make it parameterized to change how the stuff is handled at each callsite)

    //

    val struct = method.formalArgs.filter(a => a.typ.equals(Ref))
      .map(a => a.name)
      .foldLeft(new Structurer())((s, p) => s.initParameter(p))

    computeOutlineSeqn(Seq(struct), method.bodyOrAssumeFalse)
      .foreach(s => {
        println("-----")
        println(s.dump())
      })


    //    val res0 = new Structurer()
    //    val res1 = res0.initParameter("x")
    //    val res2 = res1.resolveLookup("x", Seq("a", "b", "c"))._2
    //    val res3 = res2.initVariable("y")
    //    val res4 = res3.resolveLookup("y", Seq("z"))._2
    //    val res5 = res3.performAssignment("x", Seq("a", "b"), res3.getAssignmentRef("y"))
    //
    //    println(s"RESULT FROM ASSIGNMENT:")
    //    println(res0.dump())
    //    println(res1.dump())
    //    println(res2.dump())
    //    println(res3.dump())
    //    println(res4.dump())
    //    println(res5.dump())

    //    method.body.map(b => computeOutlineSeq(assignment, b))
  }
}


/*
NOTES: 23.07.26

look for fragments that are solvable:

- strong separation logic paper (maybe) -> with magic wand and decidable

- two variable separation logic and its inner circle
   -> how small can a fragment get to still be undecidable




- template for the quantified permissions
- analyze laufvariables to guess what the templates should contain


cgis -> counter example guided inductive synthesis
- two variable types
- variables that are constant but unknown
- variables that are actually variable


use simple functions first without mutual recursion
- try to focus on requiring simple
- make loops/mutual recursion as an addon





idea: derive list segment like predicates -> from recursion in datatypes



strong separation logic (ssl):
  - how well does ssl deal with fractional permissions? still decidable?
  - how easy is it to extend the algorithm with different/more general predicates?
    -> how much does this impact the decidability

counterexample guided inductive synthesis (cegis):
  -

syntax guided program synthesis (sygus):


TODO: implement non deterministic join operation
TODO: implement heuristic predicate selection (based on complexity or relevance)
TODO: implement abduction procedure using predicate selection/abstraction



add type information tracking to add predicates for the values that are passed in

*/