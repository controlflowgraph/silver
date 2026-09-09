package viper.silver.inference.v3.knowledge

import viper.silver.ast.{Ref, Type}
import viper.silver.inference.v3.{FoldingStep, PredicateCollector, ReasoningEngine, RefoldingStep, RefoldingStrategy, Sat, UnfoldingStep, ValRef}
import viper.silver.inference.v3.ast.{AndTerm, EqCmpTerm, FieldAccTerm, GreaterCmpTerm, Ident, IntTerm, InternalMethod, LessEqCmpTerm, LogicTerm, MapTermSub, MulTerm, PermFracTerm, PredDef, PredFieldAccTerm, PredInst, PredInstAccTerm, Term, TermRewriter, TermSub, VarTerm}

import scala.collection.mutable

case class KnowledgeBase(path: Seq[(Ident, Term)], assignment: Assignment, heap: Heap, direct: DirectPermissionMask, folded: FoldedPermissionMask, info: LogicTerm, partial: Potential, fieldTypes: Map[String, Type]) {

  def constructInitialBackMapping(meth: InternalMethod, useAllVariables: Boolean): TermSub = {
    val args: Set[String] = if (!useAllVariables) {
      meth.args.map(_._1).toSet
    } else Set()
    val mapping: mutable.HashMap[Term, Term] = new mutable.HashMap()
    this.assignment.variables
      .filter(v => useAllVariables || args.contains(v._1))
      .foreach(v => {
        val source = VarTerm(v._1, v._2._2)
        val value = v._2._1.toVarTerm(v._2._2)
        mapping.put(value, source)
      })


    var open: Set[ValRef] = this.assignment.variables
      .filter(v => useAllVariables || args.contains(v._1))
      .filter(v => v._2._2 == Ref)
      .map(v => v._2._1)
      .toSet

    while (open.nonEmpty) {
      val current = open.head
      if (this.heap.initialized._1.contains(current)) {
        println(s"CURRENT: ${current}")
        println(s"MAPPING:")
        println(mapping.toSeq.map(e => e._1.pretty() + " ==> " + e._2.pretty()).mkString("\n"))
        println("- sm")
        val source = mapping(current.toVarTerm(Ref))
        val connections = this.heap.initialized._2.filter(v => v._1 == current)
        connections.foreach(c => {
          val resTyp = this.fieldTypes(c._2)
          val tmp = c._3.toVarTerm(resTyp)
          mapping.put(tmp, FieldAccTerm(source, c._2, resTyp))
        })

        // only add the values of ref fields as potential next steps
        val additional = connections
          .filter(c => this.fieldTypes(c._2) == Ref)
          .map(_._3)

        open = open.union(additional)
      }
      open = open.diff(Set(current))
    }

    MapTermSub(mapping.toMap)
  }

  def constructInfoBackMapping(): TermSub = {
    MapTermSub(constructBackMappingFromInfoTerm(this.info))
  }

  private def constructBackMappingFromInfoTerm(term: Term): Map[Term, Term] = {
    term match {
      case AndTerm(a, b) =>
        val bmA = constructBackMappingFromInfoTerm(a)
        val bmB = constructBackMappingFromInfoTerm(b)
        bmA ++ bmB
      case EqCmpTerm(v@VarTerm(n, _), b) if n.startsWith("t$") => Map((v, b))
      case _ => Map()
    }
  }

  def constructBackMapping(meth: InternalMethod, useAllVariables: Boolean): TermSub = {
    val args: Set[String] = if (!useAllVariables) {
      meth.args.map(_._1).toSet
    } else Set()
    val mapping: mutable.HashMap[Term, Term] = new mutable.HashMap()
    this.assignment.variables
      .filter(v => useAllVariables || args.contains(v._1))
      .foreach(v => {
        val source = VarTerm(v._1, v._2._2)
        val value = v._2._1.toVarTerm(v._2._2)
        mapping.put(value, source)
      })


    var open: Set[ValRef] = this.assignment.variables
      .filter(v => useAllVariables || args.contains(v._1))
      .filter(v => v._2._2 == Ref)
      .map(v => v._2._1)
      .toSet

    while (open.nonEmpty) {
      val current = open.head
      val source = mapping(current.toVarTerm(Ref))

      if (this.heap.objMap.contains(current)) {

        val obj = this.heap.objMap(current)
        val additional = obj.fields
          .filter(f => this.fieldTypes(f._1) == Ref)
          .filter(f => {
            val variable = f._2.toVarTerm(this.fieldTypes(f._1))
            !mapping.contains(variable)
          })
          .values
          .toSet

        obj.fields.foreach(f => {
          val fieldType = this.fieldTypes(f._1)
          val variable = f._2.toVarTerm(fieldType)
          if (!mapping.contains(variable)) {
            val access = FieldAccTerm(source, f._1, fieldType)
            mapping.put(variable, access)
          }
        })

        open = open.union(additional)
      }
      open = open.diff(Set(current))
    }

    mapping.foreach(e => println(s"${e._1.pretty()} ==> ${e._2.pretty()}"))
    MapTermSub(mapping.toMap)
  }

  def withAssignment(a: Assignment): KnowledgeBase = {
    KnowledgeBase(this.path, a, this.heap, this.direct, this.folded, this.info, this.partial, this.fieldTypes)
  }

  def withHeap(h: Heap): KnowledgeBase = {
    KnowledgeBase(this.path, this.assignment, h, this.direct, this.folded, this.info, this.partial, this.fieldTypes)
  }

  def update(fun: Assignment => Heap => DirectPermissionMask => FoldedPermissionMask => LogicTerm => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm)): KnowledgeBase = {
    update((a, h, d, f, i, p) => {
      val res = fun(a)(h)(d)(f)(i)
      (res._1, res._2, res._3, res._4, res._5, p)
    })
  }

  def update(f: (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential) => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential)): KnowledgeBase = {
    val res = f(this.assignment, this.heap, this.direct, this.folded, this.info, this.partial)
    KnowledgeBase(this.path, res._1, res._2, res._3, res._4, res._5, res._6, this.fieldTypes)
  }

  def withPath(ident: Ident, condition: Term): KnowledgeBase = {
    KnowledgeBase(this.path ++ Seq((ident, condition)), this.assignment, this.heap, this.direct, this.folded, this.info, this.partial, this.fieldTypes)
  }

  def pretty(): String = {
    val prettyHeap = this.heap.pretty().indent(2)
    val prettyAssignment = this.assignment.pretty().indent(2)
    val prettyDirect = this.direct.pretty().indent(2)
    val prettyFolded = this.folded.pretty().indent(2)
    val prettyDNF = this.info.pretty().indent(2)
    val prettyPot = this.partial.pretty().indent(2)
    s"assignment:\n$prettyAssignment\nheap:\n$prettyHeap\ndirect:\n$prettyDirect\nfolded:\n$prettyFolded\nfacts:\n$prettyDNF\npotential:\n${prettyPot}"
  }

  def hasEnoughPermissions(engine: ReasoningEngine, amount: Term, higher: Term): Boolean = {
    val lowSimp = TermRewriter.simplify(amount)
    val highSimp = TermRewriter.simplify(higher)
    (lowSimp, highSimp) match {
      case (PermFracTerm(IntTerm(a), IntTerm(b)), PermFracTerm(IntTerm(c), IntTerm(d))) =>
        val fracA = a.doubleValue / b.doubleValue
        val fracB = c.doubleValue / d.doubleValue
        fracA <= fracB
      case _ =>
        val proofResult = engine.prove(this, LessEqCmpTerm(amount, higher))
        proofResult == Sat
    }
  }

  // TODO: add max search depth to the re/unfolding search
  private def searchDepth: Int = 10

  def findUnfoldingStrategyInPredicate(engine: ReasoningEngine, defs: Map[String, PredDef], fa: PredInstAccTerm, instance: PredInstAccTerm): Option[RefoldingStep] = {
    val predDef = defs(instance.pred.name)
    val instantiated = predDef.instantiate(instance.pred)
    // TODO: EXTEND THE KNOWLEDGE WITH THE PURE INFORMATION WHEN UNFOLDING
    val pure = PredicateCollector.stripToPure(engine, instantiated, this)

    val direct = PredicateCollector.collectDirectPredicates(engine, instantiated, this)
    val folded = PredicateCollector.collectFoldedPredicates(engine, instantiated, this)
    val subs = folded.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, fa, v))

    val containedOnDirectLevel = folded.exists(v => v.pred.equals(fa.pred))
    val containedOnSubLevel = subs.nonEmpty

    if (containedOnDirectLevel || containedOnSubLevel) {
      Some(UnfoldingStep(instance.pred, instance.perm, subs))
    }
    else {
      None
    }
  }


  def findUnfoldingStrategyInPredicate(engine: ReasoningEngine, defs: Map[String, PredDef], fa: PredFieldAccTerm, instance: PredInstAccTerm): Option[RefoldingStep] = {
    val predDef = defs(instance.pred.name)
    val instantiated = predDef.instantiate(instance.pred)
    // TODO: EXTEND THE KNOWLEDGE WITH THE PURE INFORMATION WHEN UNFOLDING
    val pure = PredicateCollector.stripToPure(engine, instantiated, this)

    val direct = PredicateCollector.collectDirectPredicates(engine, instantiated, this)
    val folded = PredicateCollector.collectFoldedPredicates(engine, instantiated, this)
    val subs = folded.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, fa, v))

    val containedOnDirectLevel = direct.exists(v => v.exp.equals(fa.exp))
    val containedOnSubLevel = subs.nonEmpty

    if (containedOnDirectLevel || containedOnSubLevel) {
      Some(UnfoldingStep(instance.pred, instance.perm, subs))
    }
    else {
      None
    }
  }

  private def isNotZeroPerm(engine: ReasoningEngine, term: Term): Boolean = {
    val zero = PermFracTerm(IntTerm(BigInt.int2bigInt(0)), IntTerm(BigInt.int2bigInt(1)))
    engine.prove(this, GreaterCmpTerm(term, zero)) == Sat
  }

  private def isClearlyZeroPerm(t: Term): Boolean = {
    TermRewriter.simplify(t) match {
      case PermFracTerm(IntTerm(a), _) => a.equals(BigInt.int2bigInt(0))
      case _ => false
    }
  }

  def findUnfoldingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], fa: PredInstAccTerm): Option[RefoldingStrategy] = {
    // TODO: check if it is even possible that the permission amount is reachable
    val directAmount = this.folded.getAmount(fa.pred)
    if (hasEnoughPermissions(engine, fa.perm, directAmount)) {
      Some(RefoldingStrategy(Seq()))
    }
    else {
      val mapped: Seq[PredInstAccTerm] = this.folded.permissions.map(e => PredInstAccTerm(e._1, e._2))
        .filter(i => !isClearlyZeroPerm(i.perm))
        .filter(i => isNotZeroPerm(engine, i.perm))
        .toSeq

      val strats = mapped.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, fa, v))
      Some(RefoldingStrategy(strats))
    }
  }


  def findUnfoldingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], fa: PredFieldAccTerm): Option[RefoldingStrategy] = {
    // TODO: check if it is even possible that the permission amount is reachable
    val directAmount = this.direct.getAmount(fa.exp)
    if (hasEnoughPermissions(engine, fa.perm, directAmount)) {
      Some(RefoldingStrategy(Seq()))
    }
    else {
      val mapped: Seq[PredInstAccTerm] = this.folded.permissions.map(e => PredInstAccTerm(e._1, e._2))
        .filter(i => !isClearlyZeroPerm(i.perm))
        .filter(i => isNotZeroPerm(engine, i.perm))
        .toSeq

      val strats = mapped.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, fa, v))
      Some(RefoldingStrategy(strats))
    }
  }

  def unfold(engine: ReasoningEngine, defs: Map[String, PredDef], pred: PredInst, perm: Term): KnowledgeBase = {
    update(a => h => d => f => i => {
      val predDef = defs(pred.name)

      val instantiated = predDef.instantiate(pred)
      val direct = PredicateCollector.collectDirectPredicates(engine, instantiated, this)
      val folded = PredicateCollector.collectFoldedPredicates(engine, instantiated, this)
      val pure = PredicateCollector.stripToPure(engine, instantiated, this)

      val ud = direct
        .map(d => PredFieldAccTerm(d.exp, MulTerm(d.perm, perm)))
        .foldLeft(d)((a, b) => a.inhale(b))
      val uf = folded
        .map(d => PredInstAccTerm(d.pred, MulTerm(d.perm, perm)))
        .foldLeft(f.exhale(pred, perm))((a, b) => a.inhale(b))
      val ui = i.and(pure)

      (a, h, ud, uf, ui)
    })
  }

  def fold(engine: ReasoningEngine, defs: Map[String, PredDef], pred: PredInst, perm: Term): KnowledgeBase = {
    update(a => h => d => f => i => {
      val predDef = defs(pred.name)

      val instantiated = predDef.instantiate(pred)
      val direct = PredicateCollector.collectDirectPredicates(engine, instantiated, this)
      val folded = PredicateCollector.collectFoldedPredicates(engine, instantiated, this)
      val pure = PredicateCollector.stripToPure(engine, instantiated, this)

      val ud = direct
        .map(d => PredFieldAccTerm(d.exp, MulTerm(d.perm, perm)))
        .foldLeft(d)((a, b) => a.exhale(b))
      val uf = folded
        .map(d => PredInstAccTerm(d.pred, MulTerm(d.perm, perm)))
        .foldLeft(f.inhale(PredInstAccTerm(pred, perm)))((a, b) => a.exhale(b))
      val ui = i.and(pure)

      (a, h, ud, uf, ui)
    })
  }

  private def mergeRefoldingStrategyOptions(strats: Seq[Option[RefoldingStrategy]]): Option[RefoldingStrategy] = {
    strats.foldLeft(Some(Seq[RefoldingStep]()).asInstanceOf[Option[Seq[RefoldingStep]]])(
        (acc, strat) => (acc, strat) match {
          case (Some(a), Some(s)) => Some(a ++ s.steps)
          case _ => None
        })
      .map(v => RefoldingStrategy(v))
  }

  private def attemptRefolding(engine: ReasoningEngine, defs: Map[String, PredDef], f: PredInstAccTerm): Option[RefoldingStrategy] = {
    val predDef = defs(f.pred.name)

    val instantiated = predDef.instantiate(f.pred)
    val direct = PredicateCollector.collectDirectPredicates(engine, instantiated, this)
    val folded = PredicateCollector.collectFoldedPredicates(engine, instantiated, this)
    val pure = PredicateCollector.stripToPure(engine, instantiated, this)

    val mappedDirect = direct.map(d => findUnfoldingStrategy(engine, defs, d))
    val mappedFolded = folded.map(f => findRefoldingStrategy(engine, defs, f))

    mergeRefoldingStrategyOptions(mappedDirect ++ mappedFolded)
      .map(r => RefoldingStrategy(r.steps ++ Seq(FoldingStep(f.pred, f.perm))))
  }

  def findRefoldingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], f: PredInstAccTerm): Option[RefoldingStrategy] = {
    val current = this.folded.getAmount(f.pred)
    if (hasEnoughPermissions(engine, f.perm, current)) {
      Some(RefoldingStrategy(Seq()))
    } else {
      // check if the predicate can be unfolded
      val unfolding = findUnfoldingStrategy(engine, defs, f)
      // check if the predicate can be folded (potentially by unfolding some other predicate)
      val refolding = attemptRefolding(engine, defs, f)
      (unfolding, refolding) match {
        case (Some(a), Some(b)) => Some(RefoldingStrategy(a.steps ++ b.steps))
        case (Some(a), None) => Some(a)
        case (None, Some(a)) => Some(a)
        case (None, None) => None
      }
    }
  }

  def extendInfo(additional: LogicTerm): KnowledgeBase = {
    withInfo(this.info.and(additional))
  }

  def withInfo(info: LogicTerm): KnowledgeBase = {
    KnowledgeBase(
      this.path,
      this.assignment,
      this.heap,
      this.direct,
      this.folded,
      info,
      this.partial,
      this.fieldTypes
    )
  }
}