package viper.silver.inference

import viper.silver.ast._

import scala.util.parsing.json.JSON.flatten2

object PermissionInference {

  case class VariableInstantiation(mapping: Map[String, Term]) {

  }

  case class PredDef(name: String, params: Seq[String], body: TransparentPredicateTree) {

  }

  trait Term {
    def instantiate(vars: VariableInstantiation): Term
  }


  case class Ident(name: String) extends Term {
    def instantiate(vars: VariableInstantiation): Term = {
      vars.mapping.get(this.name) match {
        case Some(value) => value
        case None => this
      }
    }
  }

  case class FieldAcc(base: Term, field: String) extends Term {
    def instantiate(vars: VariableInstantiation): FieldAcc = {
      FieldAcc(this.base.instantiate(vars), this.field)
    }
  }

  case class PredInstance(name: String, values: Seq[Term]) {
    def instantiate(vars: VariableInstantiation): PredInstance = {
      PredInstance(
        this.name,
        this.values.map(v => v.instantiate(vars))
      )
    }

    def findUnfoldingStrategy(defs: Map[String, PredDef], acc: FieldAcc, depth: Int): Option[Seq[PredInstance]] = {
      if (depth <= 0) {
        println("stopping depth reached!")
        None
      }
      else {
        val pd: PredDef = defs(this.name)
        assert(pd.params.length == this.values.length, "Mismatching parameter count at predicate instantiation!")
        val vi: VariableInstantiation = VariableInstantiation(pd.params.zip(this.values).toMap)
        val insti = pd.body.instantiate(vi)
        println(s"instantiated with: ${vi}")
        println(s"got ${insti}")
        insti.findUnfoldingStrategy(defs, acc, depth - 1)
          .map(v => Seq(this) ++ v)
      }
    }
  }

  case class TransparentPredicateTree(direct: Set[FieldAcc], folded: Set[PredInstance]) {

    def instantiate(vars: VariableInstantiation): TransparentPredicateTree = {
      TransparentPredicateTree(
        this.direct.map(d => d.instantiate(vars)),
        this.folded.map(f => f.instantiate(vars))
      )
    }

    def findUnfoldingStrategy(defs: Map[String, PredDef], acc: FieldAcc, depth: Int): Option[Seq[PredInstance]] = {
      if (this.direct.contains(acc)) {
        println("field in direct")
        Some(Seq())
      }
      else {
        println(s"checking for ${acc} in folded")
        this.folded.flatMap(pi => pi.findUnfoldingStrategy(defs, acc, depth))
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

  def expToTerm(exp: Exp): Term = {
    exp match {
      case LocalVar(name, _) => Ident(name)
      case FieldAccess(rcv, field) => FieldAcc(
        expToTerm(rcv),
        field.name
      )
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

  def collectAccessRequirements(exp: Exp) : Set[FieldAcc] = {
    exp match {
//      case predicate: AccessPredicate =>
//      case InhaleExhaleExp(in, ex) =>
//      case exp: PermExp =>
      case access: LocationAccess => access match {
        case FieldAccess(rcv, field) => {
          val subs = collectAccessRequirements(rcv)
          if(subs.size == 1)
          {
            val fa = subs.toSeq.head
            Set(FieldAcc(fa, field.name), fa)
          }
          else {
            throw new IllegalStateException(s"Expected subexpression to require a single field access ${exp}")
          }
        }
        case _ => {
          throw new IllegalArgumentException(s"Unknown expression type ${exp.getClass.getName}")
        }
      }
      case _: AbstractLocalVar => Set()
      case _: Literal => Set()
//      case access: ResourceAccess =>
//      case CondExp(cond, thn, els) =>
//      case Unfolding(acc, body) =>
//      case Applying(wand, body) =>
//      case Asserting(a, body) =>
//      case Let(variable, exp, body) =>
//      case exp: QuantifiedExp =>
//      case ForPerm(variables, resource, body) =>
//      case exp: SeqExp =>
//      case exp: SetExp =>
//      case exp: MultisetExp =>
//      case exp: MapExp =>
//      case trigger: PossibleTrigger =>
//      case trigger: ForbiddenInTrigger =>
//      case app: FuncLikeApp =>
//      case exp: BinExp =>
//      case exp: UnExp =>
//      case lhs: Lhs =>
//      case exp: ExtensionExp =>
    }
  }

  def faToFA(fieldAccess: FieldAccess) : FieldAcc = {
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

  def inferMethod(defs: Map[String, PredDef], method: Method, depth: Int): Unit = {
    val startingTPT = method.pres.map(computeStartingTPT)
      .foldLeft(TransparentPredicateTree(Set(), Set()))((a, b) => a.union(b))
    println(s"STARTING TPT: ${startingTPT}")
    method.body match {
      case Some(value) => {
        value.ss.foldLeft(startingTPT)((tpt, stmt) => {
          println(s"processing: ${stmt.toString()}")
          stmt match {
            case NewStmt(lhs, fields) => {

              fields.foldLeft(tpt)((t, f) => {
                println(s"adding permission: ${lhs.name}.${f.name}")
                t.addFieldAccessPerm(FieldAcc(Ident(lhs.name), f.name))
              })
            }
            case assign: AbstractAssign => assign match {
              case LocalVarAssign(lhs, rhs) => {
                val requirements = collectAccessRequirements(rhs)
                println(s"requiring ${requirements} for the assignment")
                tpt
              }
              case FieldAssign(lhs, rhs) => {
                val requirements = collectAccessRequirements(rhs).union(Set(faToFA(lhs)))
                println(s"requiring ${requirements} for the field assignment")
                requirements.map(r => tpt.findUnfoldingStrategy(defs, r, depth))
                  .foreach(u => {
                    println(s"unfolding strategy: ${u}")
                  })

                tpt
              }
            }
//            case MethodCall(methodName, args, targets) =>
//            case Exhale(exp) =>
//            case Inhale(exp) =>
//            case Assert(exp) =>
//            case Assume(exp) =>
//            case Fold(acc) =>
//            case Unfold(acc) =>
//            case Package(wand, proofScript) =>
//            case Apply(exp) =>
//            case Seqn(ss, scopedSeqnDeclarations) =>
//            case If(cond, thn, els) =>
//            case While(cond, invs, body) =>
//            case Label(name, invs) =>
//            case Goto(target) =>
//            case LocalVarDeclStmt(decl) =>
//            case Quasihavoc(lhs, exp) =>
//            case Quasihavocall(vars, lhs, exp) =>
//            case stmt: ExtensionStmt =>
          }
        })
      }
      case None => {}
    }
  }

  def process(program: Program): Unit = {
    try {
      /*
      in order to create an unfolding strategy for a set of fields the strategies are computed separately and then merged
      merging two strategies consists of eliminating the common prefix in order to only unfold that part once
      strategies: [A, B, C] & [A, B, D]
      result: [A, B, C, D]
       */

      /*
      automatic termination criterion if the argument field length is shorter than all existing fields in the current predicate
      */
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