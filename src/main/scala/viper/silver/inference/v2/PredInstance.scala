package viper.silver.inference.v2

import viper.silver.inference.v2.ast.{FieldAcc, PredDef, Term, TermSub}

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


case class TransparentPredicateTree(direct: Set[FieldAcc], folded: Set[PredInstance]) {

  def this() = {
    this(Set(), Set())
  }

  def findRefoldingStrategy(defs: Map[String, PredDef], desiredPredicate: PredInstance, depth: Int): Option[FoldingStrategy] = {
    // TODO: introduce knowledge base to trim the implications
    // TODO: add requirements to each field access and predicate instance which indicate the implications (or empty set if not wrapped inside implication)
    //       -> filter the required stuff when there exists one knowledge piece which is 100% UNSAT (and not UNKNOWN/SAT)
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
                failures = failures.union(Set(s"failed to unfold ${direct.pretty()}"))
              }
            }
            remainingDirect = remainingDirect.diff(Set(direct))
          }

          while (remainingFolded != Set()) {
            val folded = remainingFolded.toSeq.head
            val pred = folded._1
            val remDepth = folded._2

            if (remDepth <= 0) {
              failures = failures.union(Set(s"failed to unfold by depth ${pred.pretty()}"))
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
                  println(s"sub unfolding of ${pred.pretty()} requires:")
                  res.direct.foreach(r => println(s"\tfield: ${r.pretty()}"))
                  res.folded.foreach(r => println(s"\tpred: ${r.pretty()}"))
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
    println(s">>> UNFOLDING: ${pred}")
    val predDef = defs(pred.name)
    val inst = VariableInstantiation(predDef.params.zip(pred.values).toMap)
    val instBody = predDef.body.instantiate(inst)
    TransparentPredicateTree(
      this.direct.union(instBody.direct),
      this.folded.diff(Set(pred)).union(instBody.folded)
    )
  }

  def fold(defs: Map[String, PredDef], pred: PredInstance): TransparentPredicateTree = {
    println(s">>> FOLDING: ${pred}")
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
