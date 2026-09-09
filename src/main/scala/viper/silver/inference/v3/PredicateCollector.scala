package viper.silver.inference.v3

import viper.silver.inference.v3.ast.{AndTerm, BoolTerm, EqCmpTerm, GreaterCmpTerm, GreaterEqCmpTerm, ImplTerm, LessCmpTerm, LessEqCmpTerm, LogicTerm, NotEqCmpTerm, NotTerm, OrTerm, PredFieldAccTerm, PredInstAccTerm, VarTerm}
import viper.silver.inference.v3.knowledge.KnowledgeBase

object PredicateCollector {
  def collectPotSatImpls(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): Seq[ImplTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectPotSatImpls(engine, a, kb) ++ collectPotSatImpls(engine, b, kb)
      case impl@ImplTerm(prem, _) => {
        if (engine.prove(kb, prem) == PotSat) Seq(impl)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectPotSatImpls(engine, t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectPotSatImpls(engine, a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        val includedB = collectPotSatImpls(engine, b, kb)
        if (includedB.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        Seq()
      }
      case _: PredFieldAccTerm => Seq()
      case _: PredInstAccTerm => Seq()
      case _: VarTerm => Seq()
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
      }
    }
  }


  def collectDirectPredicates(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): Seq[PredFieldAccTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectDirectPredicates(engine, a, kb) ++ collectDirectPredicates(engine, b, kb)
      case ImplTerm(prem, cons) => {
        if (engine.prove(kb, prem) == Sat) collectDirectPredicates(engine, cons, kb)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectDirectPredicates(engine, t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectDirectPredicates(engine, a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        val includedB = collectDirectPredicates(engine, b, kb)
        if (includedB.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        Seq()
      }
      case p: PredFieldAccTerm => Seq(p)
      case _: PredInstAccTerm => Seq()
      case _: VarTerm => Seq()
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
      }
    }
  }

  def stripToPure(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): LogicTerm = {
    term match {
      case v: BoolTerm => v
      case v: EqCmpTerm => v
      case v: GreaterCmpTerm => v
      case v: GreaterEqCmpTerm => v
      case v: LessCmpTerm => v
      case v: LessEqCmpTerm => v
      case v: NotEqCmpTerm => v
      case AndTerm(a, b) =>
        val dnfA = stripToPure(engine, a, kb)
        val dnfB = stripToPure(engine, b, kb)
        AndTerm(dnfA, dnfB)
      case ImplTerm(prem, cons) =>
        if (engine.prove(kb, prem) == Sat) stripToPure(engine, cons, kb)
        else BoolTerm(true)
      case NotTerm(t) => NotTerm(stripToPure(engine, t, kb))
      case OrTerm(a, b) =>
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val dnfA = stripToPure(engine, a, kb)
        val dnfB = stripToPure(engine, b, kb)
        OrTerm(dnfA, dnfB)
      case _: PredFieldAccTerm => BoolTerm(true)
      case _: PredInstAccTerm => BoolTerm(true)
      case v: VarTerm => EqCmpTerm(v, BoolTerm(true))
      case _ =>
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
    }
  }


  def collectFoldedPredicates(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): Seq[PredInstAccTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectFoldedPredicates(engine, a, kb) ++ collectFoldedPredicates(engine, b, kb)
      case ImplTerm(prem, cons) =>
        if (engine.prove(kb, prem) == Sat) collectFoldedPredicates(engine, cons, kb)
        else Seq()
      case NotTerm(t) =>
        val included = collectFoldedPredicates(engine, t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Predicates within negation!")
        }
        Seq()
      case OrTerm(a, b) =>
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectFoldedPredicates(engine, a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Predicates within disjunction!")
        }
        val includedB = collectFoldedPredicates(engine, b, kb)
        if (includedB.nonEmpty) {
          throw new IllegalArgumentException("Predicates within disjunction!")
        }
        Seq()
      case _: PredFieldAccTerm => Seq()
      case p: PredInstAccTerm => Seq(p)
      case _: VarTerm => Seq()
      case _ =>
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
    }
  }
}