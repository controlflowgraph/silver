package viper.silver.inference.v2.knowledge

import viper.silver.ast.{Exp, NeCmp, NullLit}
import viper.silver.inference.v2.ast.PredDefConstructor.expToTerm
import viper.silver.inference.v2.ast.{FieldAcc, Term, TermSub, Var}

trait Knowledge {

  def substitute(ts: TermSub): Knowledge

  def pretty() : String

  def negate(): Knowledge
}

case class IsNull(e: Term) extends Knowledge {

  def negate(): Knowledge = {
    IsNonNull(this.e)
  }

  def substitute(ts: TermSub): Knowledge = {
    IsNull(this.e.substitute(ts))
  }

  def pretty() : String= {
    this.e.pretty() + " == null"
  }
}

case class IsNonNull(e: Term) extends Knowledge {

  def negate(): Knowledge = {
    IsNull(this.e)
  }

  def substitute(ts: TermSub): Knowledge = {
    IsNonNull(this.e.substitute(ts))
  }

  def pretty() : String= {
    this.e.pretty() + " != null"
  }
}

case class Equivalence(a: Term, b: Term) {
  def pretty(): String = this.a.pretty() + " === " + this.b.pretty()

}


trait ProofResult {}

object SAT extends ProofResult {}

object UNSAT extends ProofResult {}

object UNKNOWN extends ProofResult {}

case class KnowledgeBase(knowledge: Set[Knowledge]) {

  def substitute(ts: TermSub): KnowledgeBase = {
    KnowledgeBase(this.knowledge.map(k => k.substitute(ts)))
  }

  def prove(k: Set[Knowledge]): ProofResult = {
    val mapped = k.map(a => prove(a))
    if(mapped.contains(UNSAT)){
      UNSAT
    }
    else if(mapped.contains(UNKNOWN)){
      UNKNOWN
    }
    else{
      SAT
    }
  }

  def prove(k: Knowledge): ProofResult = {
    // TODO: replace with sensible implementation
    if (this.knowledge.contains(k)) {
      SAT
    }
    else {
      UNSAT
    }
  }

  def extend(k: Knowledge): KnowledgeBase = {
    this.extend(Set(k))
  }

  def extend(k: Set[Knowledge]): KnowledgeBase = {
    KnowledgeBase(this.knowledge.union(k))
  }

  def pretty(): String = {
    "{" + this.knowledge.map(k => k.pretty()).mkString(", ") + "}"
  }
}

object Knowledge {

  def conditionToKnowledgeSet(e: Exp): Set[Knowledge] = {
    e match {
      case NeCmp(v, NullLit()) => Set(IsNonNull(expToTerm(v)))
      case NeCmp(NullLit(), v) => Set(IsNonNull(expToTerm(v)))
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract knowledge from condition ${e.getClass.getName}")
      }
    }
  }

  def collectKnowledgeAboutTerm(t: Term): Set[Knowledge] = {
    var knowledge = Set[Knowledge]()

    // add knowledge about the values inside the sub parts of the field access being nonnull
    var propped: Term = t
    while (propped.isInstanceOf[FieldAcc]) {
      val sub = propped.asInstanceOf[FieldAcc].v
      knowledge = knowledge.union(Set(IsNonNull(sub)))
      propped = sub
    }

    // if the bottom part is a variable it must be nonnull
    propped match {
      case _: Var => {
        knowledge = knowledge.union(Set(IsNonNull(propped)))
      }
    }

    knowledge
  }
}