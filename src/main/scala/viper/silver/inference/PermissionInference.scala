package viper.silver.inference

import viper.silver.ast._


case class PermissionInference(program: Program) {

  case class VariableInstantiation(mapping: Map[String, Term]) {

  }

  case class PredDef(name: String, params: Seq[String], body: TransparentPredicateTree) {
    def pretty(): String = {
      s"predicate ${this.name}(${this.params.mkString(", ")}) ${this.body.pretty()}"
    }
  }

  trait Term {
    def instantiate(vars: VariableInstantiation): Term

    def pretty(): String
  }


  case class Ident(name: String) extends Term {
    def instantiate(vars: VariableInstantiation): Term = {
      vars.mapping.get(this.name) match {
        case Some(value) => value
        case None => this
      }
    }

    def pretty(): String = {
      this.name
    }
  }

  case class FieldAcc(base: Term, field: String) extends Term {
    def instantiate(vars: VariableInstantiation): FieldAcc = {
      FieldAcc(this.base.instantiate(vars), this.field)
    }

    def pretty(): String = {
      s"${this.base.pretty()}.${this.field}"
    }
  }

  case class PredInstance(name: String, values: Seq[Term]) {
    def instantiate(vars: VariableInstantiation): PredInstance = {
      PredInstance(
        this.name,
        this.values.map(v => v.instantiate(vars))
      )
    }

    def pretty(): String = {
      s"${this.name}(${this.values.map(_.pretty()).mkString(", ")})"
    }

    def findPredInstanceUnfoldingStrategy(defs: Map[String, PredDef], pred: PredInstance, depth: Int): Option[FoldingStrategy] = {
      if (depth <= 0) {
        None
      }
      else {
        val pd: PredDef = defs(this.name)
        assert(pd.params.length == this.values.length, "Mismatching parameter count at predicate instantiation!")
        val vi: VariableInstantiation = VariableInstantiation(pd.params.zip(this.values).toMap)
        val insti = pd.body.instantiate(vi)
        insti.findPredInstanceUnfoldingStrategy(defs, pred, depth - 1)
          .map(v => FoldingStrategy(Seq(FoldingStep(unfolding = true, this)) ++ v.steps))
      }
    }

    def findUnfoldingStrategy(defs: Map[String, PredDef], acc: FieldAcc, depth: Int): Option[Seq[PredInstance]] = {
      if (depth <= 0) {
        None
      }
      else {
        val pd: PredDef = defs(this.name)
        assert(pd.params.length == this.values.length, "Mismatching parameter count at predicate instantiation!")
        val vi: VariableInstantiation = VariableInstantiation(pd.params.zip(this.values).toMap)
        val insti = pd.body.instantiate(vi)
        insti.findUnfoldingStrategy(defs, acc, depth - 1)
          .map(v => Seq(this) ++ v)
      }
    }

    def findUnfoldingStrategyForDirect(defs: Map[String, PredDef], acc: FieldAcc, depth: Int): Option[FoldingStrategy] = {
      if (depth <= 0) {
        None
      }
      else {
        val pd: PredDef = defs(this.name)
        assert(pd.params.length == this.values.length, "Mismatching parameter count at predicate instantiation!")
        val vi: VariableInstantiation = VariableInstantiation(pd.params.zip(this.values).toMap)
        val insti = pd.body.instantiate(vi)
        insti.findUnfoldingStrategyForDirect(defs, acc, depth - 1)
          .map(v => FoldingStrategy(Seq(FoldingStep(unfolding = true, this)) ++ v.steps))
      }
    }
  }

  case class FoldingStep(unfolding: Boolean, pred: PredInstance) {

  }

  case class FoldingStrategy(steps: Seq[FoldingStep]) {
    def merge(other: FoldingStrategy): FoldingStrategy = {
      FoldingStrategy((steps ++ other.steps).foldLeft((Set[FoldingStep](), Seq[FoldingStep]()))((acc, step) => {
        if (acc._1.contains(step)) {
          acc
        }
        else {
          (acc._1.union(Set(step)), acc._2 ++ Seq(step))
        }
      })._2)
    }

    def pretty(): String = {
      this.steps.map(s => (if (s.unfolding) "unfold " else "fold   ") + s.pred.pretty()).mkString("\n")
    }
  }

  case class TransparentPredicateTree(direct: Set[FieldAcc], folded: Set[PredInstance]) {

    def this() = {
      this(Set(), Set())
    }

    def findRefoldingStrategy(defs: Map[String, PredDef], desiredPredicate: PredInstance, depth: Int): Option[FoldingStrategy] = {
      val strategy = findPredInstanceUnfoldingStrategy(defs, desiredPredicate, depth)
      strategy match {
        case Some(value) => Some(value)
        case None => {
          var endingFolding = Seq[FoldingStrategy]()
          var strategies = Seq[FoldingStrategy]()
          var remainingDirect = Set[FieldAcc]()
          var remainingFolded = Set((desiredPredicate, depth))
          var failures: Set[String] = Set()
          while (remainingDirect != Set() || remainingFolded != Set()) {
            while (remainingDirect != Set()) {
              val direct = remainingDirect.toSeq.head
              val result = findUnfoldingStrategyForDirect(defs, direct, depth)
              result match {
                case Some(value) => {
                  strategies = strategies ++ Seq(value)
                }
                case None => {
                  failures = failures.union(Set(s"failed to unfold ${direct}"))
                }
              }
              remainingDirect = remainingDirect.diff(Set(direct))
            }

            while (remainingFolded != Set()) {
              val folded = remainingFolded.toSeq.head
              val pred = folded._1
              val remDepth = folded._2

              if (remDepth <= 0) {
                failures = failures.union(Set(s"failed to unfold ${pred}"))
              }
              else {
                val result = findPredInstanceUnfoldingStrategy(defs, pred, remDepth)
                result match {
                  case Some(value) => {
                    strategies = strategies ++ Seq(value)
                  }
                  case None => {
                    // instantiate
                    // add direct and folded predicates as requirement
                    val predDef = defs(pred.name)
                    val inst = VariableInstantiation(predDef.params.zip(pred.values).toMap)
                    val res = predDef.body.instantiate(inst)
                    remainingDirect = remainingDirect.union(res.direct)
                    remainingFolded = remainingFolded.union(res.folded.map(v => (v, remDepth - 1)))
                    endingFolding = Seq(FoldingStrategy(Seq(FoldingStep(unfolding = false, pred)))) ++ endingFolding
                  }
                }
              }

              remainingFolded = remainingFolded.diff(Set(folded))
            }
          }

//          println("unfolding strategies:")
//          strategies.foreach(e => println(e))
//          println()
          println("---------------------- unfolding failures ----------------------")
          failures.foreach(e => println(e))

          if (failures.isEmpty) {
            val finalFold = FoldingStrategy(Seq(FoldingStep(unfolding = false, desiredPredicate)))
            val merged = (strategies ++ endingFolding ++ Seq(finalFold))
              .foldLeft(FoldingStrategy(Seq()))((a, b) => a.merge(b))
            println(merged.pretty())
            Some(merged)
          }
          else {
            None
          }
        }
      }
    }

    def pretty(): String = {
      "{" + (this.direct.map(_.pretty()) ++ this.folded.map(_.pretty())).mkString(", ") + "}"
    }

    def unfold(defs: Map[String, PredDef], pred: PredInstance): TransparentPredicateTree = {
      val predDef = defs(pred.name)
      val inst = VariableInstantiation(predDef.params.zip(pred.values).toMap)
      val instBody = predDef.body.instantiate(inst)
      TransparentPredicateTree(
        this.direct.union(instBody.direct),
        this.folded.diff(Set(pred)).union(instBody.folded)
      )
    }

    def fold(defs: Map[String, PredDef], pred: PredInstance): TransparentPredicateTree = {
      val predDef = defs(pred.name)
      val inst = VariableInstantiation(predDef.params.zip(pred.values).toMap)
      val instBody = predDef.body.instantiate(inst)
      if(!instBody.direct.subsetOf(this.direct)) {
        sys.error(s"Not all field access permissions present when folding predicate ${pred} (missing: ${instBody.direct.diff(this.direct)})")
      }

      if(!instBody.folded.subsetOf(this.folded)) {
        sys.error(s"Not all predicate permissions present when folding predicate ${pred} (missing: ${instBody.folded.diff(this.folded)})")
      }
      TransparentPredicateTree(
        this.direct.diff(instBody.direct),
        this.folded.diff(instBody.folded).union(Set(pred))
      )
    }

    def instantiate(vars: VariableInstantiation): TransparentPredicateTree = {
      TransparentPredicateTree(
        this.direct.map(d => d.instantiate(vars)),
        this.folded.map(f => f.instantiate(vars))
      )
    }

    def findPredInstanceUnfoldingStrategy(defs: Map[String, PredDef], pred: PredInstance, depth: Int): Option[FoldingStrategy] = {
      if (this.folded.contains(pred)) {
        Some(FoldingStrategy(Seq()))
      }
      else {
        this.folded.flatMap(pi => pi.findPredInstanceUnfoldingStrategy(defs, pred, depth))
          .collectFirst(i => i)
      }
    }

    def findUnfoldingStrategy(defs: Map[String, PredDef], acc: FieldAcc, depth: Int): Option[Seq[PredInstance]] = {
      if (this.direct.contains(acc)) {
        Some(Seq())
      }
      else {
        this.folded.flatMap(pi => pi.findUnfoldingStrategy(defs, acc, depth))
          .collectFirst(i => i)
      }
    }

    def findUnfoldingStrategyForDirect(defs: Map[String, PredDef], acc: FieldAcc, depth: Int): Option[FoldingStrategy] = {
      if (this.direct.contains(acc)) {
        Some(FoldingStrategy(Seq()))
      }
      else {
        this.folded.flatMap(pi => pi.findUnfoldingStrategyForDirect(defs, acc, depth))
          .collectFirst(i => i)
      }
    }

    def union(other: TransparentPredicateTree): TransparentPredicateTree = {
      TransparentPredicateTree(
        this.direct.union(other.direct),
        this.folded.union(other.folded)
      )
    }

    def addFieldAccessPerm(acc: FieldAcc): TransparentPredicateTree = {
      union(TransparentPredicateTree(Set(acc), Set()))
    }

    def exhale(acc: FieldAcc): TransparentPredicateTree = {
      println(s"exhaling: ${acc.pretty()}")
      TransparentPredicateTree(this.direct.diff(Set(acc)), this.folded)
    }

    def exhale(pred: PredInstance): TransparentPredicateTree = {
      println(s"exhaling: ${pred.pretty()}")
      TransparentPredicateTree(this.direct, this.folded.diff(Set(pred)))
    }

    def inhale(acc: FieldAcc): TransparentPredicateTree = {
      println(s"inhaling: ${acc.pretty()}")
      TransparentPredicateTree(this.direct.union(Set(acc)), this.folded)
    }

    def inhale(pred: PredInstance): TransparentPredicateTree = {
      println(s"inhaling: ${pred.pretty()}")
      TransparentPredicateTree(this.direct, this.folded.union(Set(pred)))
    }
  }

  def locToTerm(loc: Exp): Term = {
    loc match {
      case access: LocationAccess => access match {
        case FieldAccess(rcv, field) => FieldAcc(locToTerm(rcv), field.name)
        case _ => {
          throw new IllegalArgumentException(s"Unknown expression type ${loc.getClass.getName}")
        }
      }
      case localVar: AbstractLocalVar => localVar match {
        case LocalVar(name, _) => Ident(name)
        case _ => {
          throw new IllegalArgumentException(s"Unknown expression type ${loc.getClass.getName}")
        }
      }
      case _ => {
        throw new IllegalArgumentException(s"Unknown expression type ${loc.getClass.getName}")
      }
    }
  }

  case class IntTerm(value: BigInt) extends Term {

    override def instantiate(vars: VariableInstantiation): Term = this

    override def pretty(): String = this.value.toString()
  }

  case class BoolTerm(value: Boolean) extends Term {

    override def instantiate(vars: VariableInstantiation): Term = this

    override def pretty(): String = s"${this.value}"
  }

  case class FracPerm(left: Term, right: Term) extends Term {

    override def instantiate(vars: VariableInstantiation): Term = FracPerm(
      this.left.instantiate(vars),
      this.right.instantiate(vars)
    )

    override def pretty(): String = this.left.pretty() + "/" + this.right.pretty()
  }

  def expToTerm(exp: Exp): Term = {
    exp match {
      case LocalVar(name, _) => Ident(name)
      case FieldAccess(rcv, field) => FieldAcc(
        expToTerm(rcv),
        field.name
      )
      case FractionalPerm(left, right) => FracPerm(
        expToTerm(left),
        expToTerm(right)
      )
      case IntLit(i) => IntTerm(i)
      case FalseLit() => BoolTerm(false)
      case TrueLit() => BoolTerm(true)
      case _ => {
        throw new IllegalArgumentException(s"Unknown expression type ${exp.getClass.getName} to convert to term!")
      }
    }
  }

  def collectTPTContent(exp: Exp): TransparentPredicateTree = {
    println(s"collecting: ${exp} ${exp.getClass.getName}")
    exp match {
      case And(a, b) => {
        val r1 = collectTPTContent(a)
        val r2 = collectTPTContent(b)
        r1.union(r2)
      }
      case Implies(_, b) => collectTPTContent(b) // TODO CFG: think about if there can be access predicates on the left side
      case LeCmp(_, _) => TransparentPredicateTree(Set(), Set())
      case predicate: AccessPredicate => predicate match {
        case FieldAccessPredicate(loc, _) => {
          val direct = Set(locToTerm(loc).asInstanceOf[FieldAcc])
          val folded = Set[PredInstance]()
          TransparentPredicateTree(direct, folded)
        }
        case PredicateAccessPredicate(loc, _) => {
          val direct = Set[FieldAcc]()
          val folded = Set(PredInstance(
            loc.predicateName,
            loc.args.map(expToTerm)
          ))
          TransparentPredicateTree(direct, folded)
        }
        case _ => {
          throw new IllegalArgumentException(s"Unknown expression type ${exp.getClass.getName}")
        }
      }
      case _ => {
        throw new IllegalArgumentException(s"Unknown expression type ${exp.getClass.getName}")
      }
    }
  }

  def instantiatePredicateDefs(program: Program): Map[String, PredDef] = {
    program.predicates.flatMap(p => p.body.map(v => (p.name, p.formalArgs.map(f => f.name), v))).map(p => {
        println(p._3)
        val tpt = collectTPTContent(p._3)
        (p._1, PredDef(p._1, p._2, tpt))
      })
      .toMap
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

  def collectAccessRequirements(exp: Exp): PermissionRequirements = {
    exp match {
      case _: Unfolding => PermissionRequirements(Set(), Set())
      case And(a, b) => {
        val reqA = collectAccessRequirements(a)
        val reqB = collectAccessRequirements(b)
        reqA.merge(reqB)
      }
      case LeCmp(a, b) => {
        val reqA = collectAccessRequirements(a)
        val reqB = collectAccessRequirements(b)
        reqA.merge(reqB)
      }
      case PredicateAccessPredicate(pred, permExp) => {
        PermissionRequirements(Set(), Set(PredInstance(pred.predicateName, pred.args.map(expToTerm))))
      }
      case NeCmp(a, b) => {
        val reqA = collectAccessRequirements(a)
        val reqB = collectAccessRequirements(b)
        reqA.merge(reqB)
      }
      case Implies(cond, body) => {
        val reqCond = collectAccessRequirements(cond)
        val reqBody = collectAccessRequirements(body)
        reqCond.merge(reqBody)
      }
      case FractionalPerm(_, _) => PermissionRequirements(Set(), Set())
      case access: LocationAccess => access match {
        case FieldAccess(LocalVar(name, _), field) => {
          PermissionRequirements(Set(FieldAcc(Ident(name), field.name)), Set())
        }
        case FieldAccess(rcv, field) => {
          val subs = collectAccessRequirements(rcv)
          if (subs.fields == 1) {
            val fa = subs.fields.toSeq.head
            PermissionRequirements(Set(FieldAcc(fa, field.name), fa), Set())
          }
          else {
            throw new IllegalStateException(s"Expected subexpression to require a single field access ${exp}")
          }
        }
        case _ => {
          throw new IllegalArgumentException(s"Unknown expression type ${exp.getClass.getName}")
        }
      }
      case _: AbstractLocalVar => PermissionRequirements(Set(), Set())
      case _: Literal => PermissionRequirements(Set(), Set())
    }
  }

  def faToFA(fieldAccess: FieldAccess): FieldAcc = {
    FieldAcc(expToTerm(fieldAccess.rcv), fieldAccess.field.name)
  }

  def computeStartingTPT(exp: Exp): TransparentPredicateTree = {
    exp match {
      case predicate: AccessPredicate => predicate match {
        case FieldAccessPredicate(loc, permExp) => {
          TransparentPredicateTree(Set(FieldAcc(expToTerm(loc.rcv), loc.field.name)), Set())
        }
        case PredicateAccessPredicate(loc, permExp) => {
          val name = loc.predicateName
          val values = loc.args.map(expToTerm)
          TransparentPredicateTree(Set(), Set(PredInstance(name, values)))
        }
      }
      case And(a, b) => {
        val tptA = computeStartingTPT(a)
        val tptB = computeStartingTPT(b)
        tptA.union(tptB)
      }
      case _: LeCmp => {
        // TODO CFG: check if there the subs can contain relevant predicate information
        TransparentPredicateTree(Set(), Set())
      }
      case _: Literal => {
        TransparentPredicateTree(Set(), Set())
      }
      case Implies(left, right) => {
        // TODO CFG: retain implication information
        TransparentPredicateTree(Set(), Set())
      }
    }
  }

  def applyUnfoldingStrategies(defs: Map[String, PredDef], tpt: TransparentPredicateTree, strategy: FoldingStrategy): TransparentPredicateTree = {

    strategy.steps.foldLeft(tpt)((state, strat) => {
      if(strat.unfolding){
        state.unfold(defs, strat.pred)
      }
      else {
        state.fold(defs, strat.pred)
      }
    })
//      strat.foldLeft(state)((curr, pred) => {
//        if (curr._2.contains(pred)) {
//          curr
//        }
//        else {
//          (curr._1.unfold(defs, pred), curr._2.union(Set(pred)))
//        }
//      })
//    })._1
  }

  def getUnfoldingStrategiesForAllRequirements(depth: Int, tpt: TransparentPredicateTree, defs: Map[String, PredDef], requirements: PermissionRequirements): Option[FoldingStrategy] = {
    val start: Option[FoldingStrategy] = Some(FoldingStrategy(Seq()))
    val reqs1 = requirements.fields.map(r => (r.pretty(), tpt.findUnfoldingStrategyForDirect(defs, r, depth)))
    val reqs2 = requirements.predicates.map(p => (p.pretty(), tpt.findRefoldingStrategy(defs, p, depth)))
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

  def inferMethod(defs: Map[String, PredDef], method: Method, depth: Int): Unit = {
    println("===============================================================")
    println("infering method:")
    println(method)
    val startingTPT = method.pres.map(computeStartingTPT)
      .foldLeft(TransparentPredicateTree(Set(), Set()))((a, b) => a.union(b))
    method.body match {
      case Some(value) => {
        val afterTPT = value.ss.foldLeft(startingTPT)((tpt, stmt) => {
          // map each statement to the folding and unfolding operations
          println(s"${tpt.pretty()}")
          println(s">> ${stmt}")
          stmt match {
            case NewStmt(lhs, fields) => {

              fields.foldLeft(tpt)((t, f) => {
                t.addFieldAccessPerm(FieldAcc(Ident(lhs.name), f.name))
              })
            }
            case MethodCall(name, args, targets) => {
              //              println(":::::METHOD CALL:::::")
              //              println(s"name: ${name}")
              //              println(s"args: ${args}")
              //              println(s"targets: ${targets}")
              // TODO CFG:
              //  obtain the method from the list
              //  collect all preconditions -> exhale permissions
              //        ->> replace the variables of the parameters in the requirements with the arguments
              //  collect all postconditions -> inhale permissions
              //        ->> replace the variables in the post conditions with the values passed into them
              val method = program.methods.find(m => m.name.equals(name)).get
              val methodArgNames = method.formalArgs.map(_.name)
              val init = VariableInstantiation(methodArgNames.zip(args.map(expToTerm)).toMap)
              val requirements = method.pres.map(collectAccessRequirements)
                .foldLeft(PermissionRequirements(Set(), Set()))((a, b) => a.merge(b))
                .substitute(init)


              println("CURRENT TPT:")
              println(tpt.pretty())

              println(s"REQUIREMENTS:")
              println("\tfields:")
              requirements.fields.foreach(f => println(s"\t\t${f.pretty()}"))
              println("\tpredicates:")
              requirements.predicates.foreach(f => println(s"\t\t${f.pretty()}"))

              val strats = getUnfoldingStrategiesForAllRequirements(depth, tpt, defs, requirements)

              val unfolded = strats match {
                case Some(value) => applyUnfoldingStrategies(defs, tpt, value)
                case None => {
                  sys.error("Unable to find unfolding strategy for all requirements!")
                }
              }


              val retInit = VariableInstantiation(method.formalReturns.map(f => f.name).zip(targets.map(l => Ident(l.name))).toMap)
              val posts = method.posts.map(collectAccessRequirements)
                .foldLeft(PermissionRequirements(Set(), Set()))((a, b) => a.merge(b))
                .substitute(retInit)
              val fieldsExhaled = requirements.fields.foldLeft(unfolded)((a, b) => a.exhale(b))
              val exhaled = requirements.predicates.foldLeft(fieldsExhaled)((a, b) => a.exhale(b))

              val fieldsInhaled = posts.fields.foldLeft(exhaled)((a, b) => a.inhale(b))
              val inhaled = posts.predicates.foldLeft(fieldsInhaled)((a, b) => a.inhale(b))
              inhaled
            }
            case assign: AbstractAssign => assign match {
              case LocalVarAssign(lhs, rhs) => {
                // assuming access permission for variable is guaranteed
                val requirements = collectAccessRequirements(rhs)
                val reqs = getUnfoldingStrategiesForAllRequirements(depth, tpt, defs, requirements)
                reqs match {
                  case Some(value) => applyUnfoldingStrategies(defs, tpt, value)
                  case None => {
                    sys.error("Unable to find unfolding strategy for all requirements!")
                  }
                }
              }
              case FieldAssign(lhs, rhs) => {
                val requirements = collectAccessRequirements(rhs).withField(faToFA(lhs))
                //                println(s"requiring ${requirements} for the field assignment")
                val reqs = getUnfoldingStrategiesForAllRequirements(depth, tpt, defs, requirements)

                //                println("collected unfolding strategies:")

                reqs match {
                  case Some(value) => applyUnfoldingStrategies(defs, tpt, value)
                  case None => {
                    sys.error("Unable to find unfolding strategy for all requirements!")
                  }
                }
              }
            }
          }
        })
        println(s"${afterTPT.pretty()}")
      }
      case None => {}
    }
  }

  def process(): Unit = {
    try {
      /*
      in order to create an unfolding strategy for a set of fields the strategies are computed separately and then merged
      merging two strategies consists of eliminating the common prefix in order to only unfold that part once
      strategies: [A, B, C] & [A, B, D]
      result: [A, B, C, D]
       */

      /*
      automatic termination criterion if the argument field length is shorter than all existing fields in the current predicate

      x.next.value => List(???) => ???.value     List(???.next) List(???.next.value)

      which assumptions are made about the predicates?
      */

      /*
      retrieval of required permissions from preconditions with implications is not trivial based on the current state

      tracking state of variables null/nonnull
      -> sometimes implicit nonnull requirement based on the permission to a field of the given variable
      */

      /*
      no normalized layer in which all complex operations are replaced with inhale/exhale operations
      -> maybe introduce such a view in order to simplify the analysis and have fewer distinct cases
      -> only have inhale/exhale/assert/havoc

      field access --> assert
      method call --> exhale + inhale
      new --> inhale
      assignment

      + einfache expressions

      feldzugriff auf einer ebene -> normalisierung
      sequencing
      non det branching

      perms for A & perms for B
      {
        assume cond
      }
      {
        assume !cond
      }

      perms after A | perms after B

      */

      /*
      backpropagation of additional permissions that are requires
      -> how to handle permission abduction within the local scope?

      ->> silicon forward pass + carbon backward pass -> differing errors?
      */
      println("--------------------------")
      println("--------- TTTT -----------")
      println("--------------------------")


      val ddd = Seq(
        ("A", PredDef("A", Seq("this"), TransparentPredicateTree(
          Set(FieldAcc(Ident("this"), "value")),
          Set()
        ))),
        ("B", PredDef("B", Seq("this"), TransparentPredicateTree(
          Set(FieldAcc(Ident("this"), "value")),
          Set(PredInstance("C", Seq(Ident("this"))))
        ))),
        ("C", PredDef("C", Seq("this"), TransparentPredicateTree(
          Set(FieldAcc(Ident("this"), "additional")),
          Set()
        )))
      ).toMap
      println("PREDICATE DEFINITIONS:")
      println(ddd.map(d => d._2.pretty()).mkString("\n"))
      val ttt = TransparentPredicateTree(Set(FieldAcc(Ident("x"), "additional")), Set(PredInstance("A", Seq(Ident("x")))))
      val result = ttt.findRefoldingStrategy(ddd, PredInstance("B", Seq(Ident("x"))), 10)
      println(s"RESULT OF REFOLDING: ${result}")

      println("---------------------")


      val defs = instantiatePredicateDefs(program)
      val tpt = TransparentPredicateTree(Set(), Set(PredInstance("Cont$$_$$$$_T$$$$_", Seq(Ident("y")))))
      println("--------------------")
      println(s"PRED DEF RESULT: ${defs}")
      println("--------------------")
      println(s"STARTING WITH: ${tpt}")
      val res = tpt.findUnfoldingStrategy(defs, FieldAcc(Ident("y"), "Cont$$_$$$$_T$$$$_$$$value"), 10)
      println(s"UNFOlDING STRATEGY RESULT: ${res}")
      println("--------------------")
      program.methods.foreach(inferMethod(defs, _, 10))
      println("--------------------")
      println("--------------------")

      sys.error("FINISHED")
    }
    catch {
      case e: Exception => {
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
        println(e.toString)
        e.getStackTrace.toList.take(100).foreach(println)
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
      }

    }
  }
}