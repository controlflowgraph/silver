package viper.silver.inference.v2

import viper.silver.ast.{Injection, Stmt}
import viper.silver.inference.v2.ast.{FieldAcc, PredDef, Term, TermSub}
import viper.silver.inference.v2.knowledge.{Knowledge, KnowledgeBase, SAT}

case class PredInstance(name: String, values: Seq[Term]) {
  def substitute(es: TermSub): PredInstance = {
    PredInstance(this.name, this.values.map(_.substitute(es)))
  }

  def instantiate(vars: VariableInstantiation) : PredInstance = {
    PredInstance(this.name, this.values.map(v => v.instantiate(vars)))
  }


  def pretty(): String = {
    s"${this.name}(${this.values.map(_.pretty()).mkString(", ")})"
  }

  def findPredInstanceUnfoldingStrategy(defs: Map[String, PredDef], kb: KnowledgeBase, pred: PredInstance, depth: Int): Option[FoldingStrategy] = {
    if (depth <= 0) {
      None
    }
    else {
      val pd: PredDef = defs(this.name)
      assert(pd.params.length == this.values.length, "Mismatching parameter count at predicate instantiation!")
      val vi: VariableInstantiation = VariableInstantiation(pd.params.zip(this.values).toMap)
      val insti = pd.body.instantiate(vi)
      insti.findPredInstanceUnfoldingStrategy(defs, kb, pred, depth - 1)
        .map(v => FoldingStrategy(Seq(FoldingStep(unfolding = true, this)) ++ v.steps))
    }
  }

  def findUnfoldingStrategy(defs: Map[String, PredDef], kb: KnowledgeBase, acc: FieldAcc, depth: Int): Option[Seq[PredInstance]] = {
    if (depth <= 0) {
      None
    }
    else {
      val pd: PredDef = defs(this.name)
      assert(pd.params.length == this.values.length, "Mismatching parameter count at predicate instantiation!")
      val vi: VariableInstantiation = VariableInstantiation(pd.params.zip(this.values).toMap)
      val insti = pd.body.instantiate(vi)
      insti.findUnfoldingStrategy(defs, kb, acc, depth - 1)
        .map(v => Seq(this) ++ v)
    }
  }

  def findUnfoldingStrategyForDirect(defs: Map[String, PredDef], ts: TermSub, kb: KnowledgeBase, acc: FieldAcc, depth: Int): Option[FoldingStrategy] = {
    if (depth <= 0) {
      None
    }
    else {
      val pd: PredDef = defs(this.name)
      assert(pd.params.length == this.values.length, "Mismatching parameter count at predicate instantiation!")
      val vi: VariableInstantiation = VariableInstantiation(pd.params.zip(this.values).toMap)
      val insti = pd.body.instantiate(vi)
      insti.findUnfoldingStrategyForDirect(defs, ts, kb, acc, depth - 1)
        .map(v => FoldingStrategy(Seq(FoldingStep(unfolding = true, this)) ++ v.steps))
    }
  }
}


case class TransparentPredicateTree(foldingStory: Seq[(Injection, FoldingStep)], direct: Set[(Set[Knowledge], FieldAcc)], folded: Set[(Set[Knowledge], PredInstance)]) {

  def this() = {
    this(Seq(), Set(), Set())
  }

  def findRefoldingStrategy(defs: Map[String, PredDef], ts: TermSub, kb: KnowledgeBase, desiredPredicate: PredInstance, depth: Int): Option[FoldingStrategy] = {
    // TODO: introduce knowledge base to trim the implications
    // TODO: add requirements to each field access and predicate instance which indicate the implications (or empty set if not wrapped inside implication)
    //       -> filter the required stuff when there exists one knowledge piece which is 100% UNSAT (and not UNKNOWN/SAT)
    val strategy = findPredInstanceUnfoldingStrategy(defs, kb, desiredPredicate, depth)
    strategy match {
      case Some(value) => Some(value)
      case None => {
        // TODO: this refolding logic might be overly restrictive
        //       -> when one option of unfolding fails everything fails
        //       -> there could be multiple ways of unfolding predicates to get
        //          a specific permission while only permitting

        var endingFolding = Seq[FoldingStrategy]()
        var strategies = Seq[FoldingStrategy]()
        var remainingDirect = Set[(Set[Knowledge], FieldAcc)]()
        var remainingFolded = Set[(Set[Knowledge], PredInstance, Int)]((Set(), desiredPredicate, depth))
        var failures: Set[String] = Set()
        while (remainingDirect != Set() || remainingFolded != Set()) {
          while (remainingDirect != Set()) {
            val direct = remainingDirect.toSeq.head
            // TODO: potentially extend the current knowledge base when proving that a specific permission inside an implication exists
            val result = findUnfoldingStrategyForDirect(defs, ts, kb, direct._2, depth)
            result match {
              case Some(value) => {
                strategies = strategies ++ Seq(value)
              }
              case None => {
                failures = failures.union(Set(s"failed to unfold ${direct._2.pretty()}"))
              }
            }
            remainingDirect = remainingDirect.diff(Set(direct))
          }

          while (remainingFolded != Set()) {
            val folded = remainingFolded.toSeq.head
            val know = folded._1 // TODO: short circuit when know is not sat
            val pred = folded._2
            val remDepth = folded._3

            if (remDepth <= 0) {
              failures = failures.union(Set(s"failed to unfold by depth ${pred.pretty()}"))
            }
            else {
              val result = findPredInstanceUnfoldingStrategy(defs, kb, pred, remDepth)
              result match {
                case Some(value) => {
                  strategies = strategies ++ Seq(value)
                }
                case None => {
                  // instantiate
                  // add direct and folded predicates as requirement
                  val predDef = defs(pred.name)
                  val inst = VariableInstantiation(predDef.params.zip(pred.values).toMap)
                  val resBefore = predDef.body.instantiate(inst)
                  val res = resBefore.substitute(ts)
//                  println(s"sub unfolding of ${pred.pretty()} requires:")
//                  res.direct.foreach(r => println(s"\tfield: { ${formatKnowledgeSet(r._1)} } ${r._2.pretty()}"))
//                  res.folded.foreach(r => println(s"\tpred: { ${formatKnowledgeSet(r._1)} } ${r._2.pretty()}"))
                  remainingDirect = remainingDirect.union(res.direct)
                  remainingFolded = remainingFolded.union(res.folded.map(v => (v._1, v._2, remDepth - 1)))
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
        if(!failures.isEmpty){
          println(s"---------------------- unfolding failures [${failures.size}] ----------------------")
          failures.foreach(e => println(e))
          println(s"----------------------------------------------${"-" * ("" + failures.size).length}----------------------")
        }

        if (failures.isEmpty) {
          val finalFold = FoldingStrategy(Seq(FoldingStep(unfolding = false, desiredPredicate)))
          val merged = (strategies ++ endingFolding ++ Seq(finalFold))
            .foldLeft(FoldingStrategy(Seq()))((a, b) => a.merge(b))
//          println(merged.pretty())
          Some(merged)
        }
        else {
          None
        }
      }
    }
  }

  private def formatKnowledgeSet(k: Set[Knowledge]) : String = {
    "{" + k.map(k => k.pretty()).mkString(", ") + "}"
  }

  def pretty(): String = {
    "{" + (this.direct.map(t => formatKnowledgeSet(t._1) + " " + t._2.pretty()) ++ this.folded.map(t => formatKnowledgeSet(t._1) + t._2.pretty())).mkString(", ") + "}"
  }

  def unfold(location: Injection, defs: Map[String, PredDef], ts: TermSub, pred: PredInstance): TransparentPredicateTree = {
//    println(s">>> UNFOLDING: ${pred}")
    val predDef = defs(pred.name)
    println(s"PRED DEF: ${predDef.body.pretty()}")
    val inst = VariableInstantiation(predDef.params.zip(pred.values).toMap)
    println(s"INSTANTIATION: ${inst}")
    val instBody = predDef.body
      .instantiate(inst)
      .substitute(ts)
    println(s"INST BODY FOLDED: ${instBody.folded}")
    TransparentPredicateTree(
      this.foldingStory ++ Seq((location, FoldingStep(unfolding = true, pred))),
      this.direct.union(instBody.direct),
      this.folded.filter(t => !(t._2.equals(pred))).union(instBody.folded)
    )
  }

  def fold(location: Injection, defs: Map[String, PredDef], ts: TermSub, pred: PredInstance, knowledge: Set[Knowledge]): TransparentPredicateTree = {
//    println(s">>> FOLDING: ${pred}")
    val predDef = defs(pred.name)
    val inst = VariableInstantiation(predDef.params.zip(pred.values).toMap)
    val instBody = predDef.body
      .instantiate(inst)
      .substitute(ts)
    if(!instBody.direct.subsetOf(this.direct)) {
      sys.error(s"Not all field access permissions present when folding predicate ${pred.pretty()} (missing: ${instBody.direct.diff(this.direct)})")
    }

    if(!instBody.folded.subsetOf(this.folded)) {
      sys.error(s"Not all predicate permissions present when folding predicate ${pred.pretty()} (missing: ${instBody.folded.diff(this.folded)})")
    }
    TransparentPredicateTree(
      this.foldingStory ++ Seq((location, FoldingStep(unfolding = false, pred))),
      this.direct.diff(instBody.direct),
      this.folded.diff(instBody.folded).union(Set((knowledge, pred)))
    )
  }

  def instantiate(vars: VariableInstantiation): TransparentPredicateTree = {
    TransparentPredicateTree(
      this.foldingStory,
      this.direct.map(d => (instKSet(d._1, vars), d._2.instantiate(vars))),
      this.folded.map(f => (instKSet(f._1, vars), f._2.instantiate(vars)))
    )
  }

  def instKSet(knowledge: Set[Knowledge], vars: VariableInstantiation) : Set[Knowledge] = {
    knowledge.map(k => k.instantiate(vars))
  }

  def findPredInstanceUnfoldingStrategy(defs: Map[String, PredDef], kb: KnowledgeBase, pred: PredInstance, depth: Int): Option[FoldingStrategy] = {
    if (this.folded.exists(t => t._2.equals(pred))) {
      Some(FoldingStrategy(Seq()))
    }
    else {
      this.folded.filter(pi => kb.prove(pi._1) == SAT)
        .flatMap(pi => pi._2.findPredInstanceUnfoldingStrategy(defs, kb, pred, depth))
        .collectFirst(i => i)
    }
  }

  def findUnfoldingStrategy(defs: Map[String, PredDef], kb: KnowledgeBase, acc: FieldAcc, depth: Int): Option[Seq[PredInstance]] = {
    if (this.direct.exists(d => d._2.equals(acc))) {
      Some(Seq())
    }
    else {
      this.folded
        .filter(pi => kb.prove(pi._1) == SAT)
        .flatMap(pi => pi._2.findUnfoldingStrategy(defs, kb, acc, depth))
        .collectFirst(i => i)
    }
  }

  def findUnfoldingStrategyForDirect(defs: Map[String, PredDef], ts: TermSub, kb: KnowledgeBase, acc: FieldAcc, depth: Int): Option[FoldingStrategy] = {
    if (this.direct.exists(d => d._2.equals(acc))) {
      Some(FoldingStrategy(Seq()))
    }
    else {
      this.folded
        .filter(pi => kb.prove(pi._1) == SAT)
        .flatMap(pi => pi._2.findUnfoldingStrategyForDirect(defs, ts, kb, acc, depth))
        .collectFirst(i => i)
    }
  }

  def union(other: TransparentPredicateTree): TransparentPredicateTree = {
    TransparentPredicateTree(
      this.foldingStory ++ other.foldingStory,
      this.direct.union(other.direct),
      this.folded.union(other.folded)
    )
  }

  def addFieldAccessPerm(acc: FieldAcc): TransparentPredicateTree = {
    union(TransparentPredicateTree(Seq(), Set((Set(), acc)), Set()))
  }

  def exhale(acc: FieldAcc): TransparentPredicateTree = {
//    println(s"exhaling: ${acc.pretty()}")
    TransparentPredicateTree(this.foldingStory, this.direct.filter(t => !(t._2.equals(acc))), this.folded)
  }

  def exhale(pred: PredInstance): TransparentPredicateTree = {
//    println(s"exhaling: ${pred.pretty()}")
    TransparentPredicateTree(this.foldingStory, this.direct, this.folded.filter(t => !(t._2.equals(pred))))
  }

  def inhale(acc: FieldAcc): TransparentPredicateTree = this.inhale(Set(), acc)

  def inhale(knowledge: Set[Knowledge], acc: FieldAcc): TransparentPredicateTree = {
//    println(s"inhaling: ${acc.pretty()}")
    TransparentPredicateTree(this.foldingStory, this.direct.union(Set((knowledge, acc))), this.folded)
  }

  def inhale(pred: PredInstance): TransparentPredicateTree = this.inhale(Set(), pred)

  def inhale(knowledge: Set[Knowledge], pred: PredInstance): TransparentPredicateTree = {
//    println(s"inhaling: ${pred.pretty()}")
    TransparentPredicateTree(this.foldingStory, this.direct, this.folded.union(Set((knowledge, pred))))
  }

  def subKSet(knowledge: Set[Knowledge], ts: TermSub): Set[Knowledge] = {
    println(s"substituting knowledge set: ${knowledge} with ${ts}")
    knowledge.map(_.substitute(ts))
  }

  def substitute(ts: TermSub): TransparentPredicateTree = {
    // TODO: think about how to apply the substitution to the fields since only variables should be renamed
    TransparentPredicateTree(
      this.foldingStory,
      this.direct.map(d => {
        val mappedPred = d._2.substitute(ts)
        mappedPred match {
          case acc: FieldAcc => (subKSet(d._1, ts), acc)
          case _ => (subKSet(d._1, ts), d._2)
        }
      }),
      this.folded.map(f => {
        (subKSet(f._1, ts), f._2.substitute(ts))
      })
    )
  }
}
