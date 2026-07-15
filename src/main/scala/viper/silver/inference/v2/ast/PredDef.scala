package viper.silver.inference.v2.ast

import viper.silver.ast.{AbstractLocalVar, AccessPredicate, And, Exp, FalseLit, FieldAccess, FieldAccessPredicate, FractionalPerm, Implies, IntLit, LeCmp, LocalVar, LocationAccess, PredicateAccessPredicate, Program, TrueLit}
import viper.silver.inference.v2.knowledge.{Knowledge, KnowledgeBase}
import viper.silver.inference.v2.{PredInstance, TransparentPredicateTree}

case class PredDef(name: String, params: Seq[String], body: TransparentPredicateTree) {
  def pretty(): String = {
    s"predicate ${this.name}(${this.params.mkString(", ")}) ${this.body.pretty()}"
  }
}


object PredDefConstructor {
  def locToTerm(loc: Exp): Term = {
    println(s"loc to term -> ${loc} => ${loc.typ}")
    loc match {
      case access: LocationAccess => access match {
        case p@FieldAccess(rcv, field) => FieldAcc(locToTerm(rcv), field.name, p.typ)
        case _ => {
          throw new IllegalArgumentException(s"Unknown expression type ${loc.getClass.getName}")
        }
      }
      case localVar: AbstractLocalVar => localVar match {
        case p@LocalVar(name, _) => Var(name, p.typ)
        case _ => {
          throw new IllegalArgumentException(s"Unknown expression type ${loc.getClass.getName}")
        }
      }
      case _ => {
        throw new IllegalArgumentException(s"Unknown expression type ${loc.getClass.getName}")
      }
    }
  }



  def collectTPTContent(exp: Exp): TransparentPredicateTree = {
//    println(s"collecting: ${exp} ${exp.getClass.getName}")
    exp match {
      case And(a, b) => {
        val r1 = collectTPTContent(a)
        val r2 = collectTPTContent(b)
        r1.union(r2)
      }
      case Implies(cond, body) => {
        // TODO CFG: think about if there can be access predicates on the left side
        val base = Knowledge.conditionToKnowledgeSet(cond)
        val tpt = collectTPTContent(body)
        val mappedDirect = tpt.direct.map(v => (base.union(v._1), v._2))
        val mappedFolded = tpt.folded.map(v => (base.union(v._1), v._2))
        TransparentPredicateTree(Seq(), mappedDirect, mappedFolded)
      }
      case LeCmp(_, _) => TransparentPredicateTree(Seq(), Set(), Set())
      case predicate: AccessPredicate => predicate match {
        case FieldAccessPredicate(loc, _) => {
          val direct = Set[(Set[Knowledge], FieldAcc)]((Set(), locToTerm(loc).asInstanceOf[FieldAcc]))
          val folded = Set[(Set[Knowledge], PredInstance)]()
          TransparentPredicateTree(Seq(), direct, folded)
        }
        case p@PredicateAccessPredicate(loc, _) => {
          val direct = Set[(Set[Knowledge], FieldAcc)]()
          val folded = Set[(Set[Knowledge], PredInstance)]((Set(), PredInstance(
            loc.predicateName,
            loc.args.map(expToTerm)
          )))
          TransparentPredicateTree(Seq(), direct, folded)
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

  def expToTerm(exp: Exp): Term = {
    exp match {
      case p@LocalVar(name, _) => Var(name, p.typ)
      case p@FieldAccess(rcv, field) => FieldAcc(
        expToTerm(rcv),
        field.name,
        p.typ
      )
      case p@FractionalPerm(left, right) => FracPerm(
        expToTerm(left),
        expToTerm(right),
        p.typ
      )
      case p@IntLit(i) => IntTerm(i, p.typ)
      case p@FalseLit() => BoolTerm(value = false, p.typ)
      case p@TrueLit() => BoolTerm(value = true, p.typ)
      case _ => {
        throw new IllegalArgumentException(s"Unknown expression type ${exp.getClass.getName} to convert to term!")
      }
    }
  }


  def constructPredicateDefs(program: Program): Map[String, PredDef] = {
    println(s"program predicates: ${
      program.predicates
    }")
    program.predicates.flatMap(p => p.body.map(v => (p.name, p.formalArgs.map(f => f.name), v))).map(p => {
        println(p._3)
        val tpt = collectTPTContent(p._3)
        (p._1, PredDef(p._1, p._2, tpt))
      })
      .toMap
  }
}