package viper.silver.inference.v3.knowledge

import viper.silver.ast.{Perm, Ref, Type}
import viper.silver.inference.v3.{ApplyStep, FoldingStep, MagicWandManager, PackageStep, PotSat, PredicateCollector, ReasoningEngine, RefCounter, RefoldingStep, RefoldingStrategy, Sat, TermNormalization, UnSat, UnfoldingStep, ValRef}
import viper.silver.inference.v3.ast.{AddTerm, AndTerm, BaguetteMagic, BoolTerm, CondTerm, EqCmpTerm, FieldAccTerm, GreaterCmpTerm, Ident, ImplTerm, IntTerm, InternalMethod, LessEqCmpTerm, LogicTerm, LogicTermRewriting, MapTermSub, MulTerm, PermAmount, PermFracTerm, PredDef, PredFieldAccTerm, PredInst, PredInstAccTerm, SubTerm, Term, TermRewriter, TermSub, VarTerm}

import scala.collection.mutable

case class KnowledgeBase(path: Seq[(Ident, Term)], assignment: Assignment, heap: Heap, direct: DirectPermissionMask, folded: FoldedPermissionMask, info: LogicTerm, partial: Potential, mwm: MagicWandManager, fieldTypes: Map[String, Type]) {

  def this(fieldTypes: Map[String, Type], rc: RefCounter) = {
    this(Seq(), new Assignment(rc), new Heap(rc), new DirectPermissionMask(), new FoldedPermissionMask(), BoolTerm(true), new Potential(), new MagicWandManager(), fieldTypes)
  }

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
        //        println(s"CURRENT: ${current}")
        //        println(s"MAPPING:")
        //        println(mapping.toSeq.map(e => e._1.pretty() + " ==> " + e._2.pretty()).mkString("\n"))
        //        println("- sm")
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

    MapTermSub(mapping.toMap)
  }

  def withAssignment(a: Assignment): KnowledgeBase = {
    KnowledgeBase(this.path, a, this.heap, this.direct, this.folded, this.info, this.partial, this.mwm, this.fieldTypes)
  }

  def withHeap(h: Heap): KnowledgeBase = {
    KnowledgeBase(this.path, this.assignment, h, this.direct, this.folded, this.info, this.partial, this.mwm, this.fieldTypes)
  }

  def update(fun: Assignment => Heap => DirectPermissionMask => FoldedPermissionMask => LogicTerm => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm)): KnowledgeBase = {
    update((a, h, d, f, i, p) => {
      val res = fun(a)(h)(d)(f)(i)
      (res._1, res._2, res._3, res._4, res._5, p)
    })
  }

  def update(f: (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential) => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential)): KnowledgeBase = {
    val res = f(this.assignment, this.heap, this.direct, this.folded, this.info, this.partial)
    KnowledgeBase(this.path, res._1, res._2, res._3, res._4, res._5, res._6, this.mwm, this.fieldTypes)
  }

  def update(f: (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential, MagicWandManager) => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential, MagicWandManager)): KnowledgeBase = {
    val res = f(this.assignment, this.heap, this.direct, this.folded, this.info, this.partial, this.mwm)
    KnowledgeBase(this.path, res._1, res._2, res._3, res._4, res._5, res._6, res._7, this.fieldTypes)
  }

  def withPath(ident: Ident, condition: Term): KnowledgeBase = {
    KnowledgeBase(this.path ++ Seq((ident, condition)), this.assignment, this.heap, this.direct, this.folded, this.info, this.partial, this.mwm, this.fieldTypes)
  }

  def pretty(): String = {
    val prettyHeap = this.heap.pretty().indent(2)
    val prettyAssignment = this.assignment.pretty().indent(2)
    val prettyDirect = this.direct.pretty().indent(2)
    val prettyFolded = this.folded.pretty().indent(2)
    val prettyDNF = this.info.pretty().indent(2)
    val prettyPot = this.partial.pretty().indent(2)
    val prettyMag = this.mwm.pretty().indent(2)
    s"assignment:\n$prettyAssignment\nheap:\n$prettyHeap\ndirect:\n$prettyDirect\nfolded:\n$prettyFolded\nfacts:\n$prettyDNF\npotential:\n${prettyPot}\nbaguettes:\n${prettyMag}"
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
        // this is problematic when having method stubs with malformed contracts
        //        val proofResult = engine.prove(this, LessEqCmpTerm(amount, higher))
        val proofResult = engine.provePure(this, LessEqCmpTerm(amount, higher))
        println(s"${}")
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


  def findUnfoldingStrategyInPredicate(engine: ReasoningEngine, defs: Map[String, PredDef], impl: ImplTerm, instance: PredInstAccTerm): Option[RefoldingStep] = {
    val predDef = defs(instance.pred.name)
    val instantiated = predDef.instantiate(instance.pred)
    // TODO: EXTEND THE KNOWLEDGE WITH THE PURE INFORMATION WHEN UNFOLDING
    val pure = PredicateCollector.stripToPure(engine, instantiated, this)

    val direct = PredicateCollector.collectDirectPredicates(engine, instantiated, this)
    val folded = PredicateCollector.collectFoldedPredicates(engine, instantiated, this)
    val partial = PredicateCollector.collectPotSatImpls(engine, instantiated, this)
    val subs = folded.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, impl, v))

    val containedOnDirectLevel = partial.exists(v => v.equals(impl))
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
    engine.provePure(this, GreaterCmpTerm(term, zero)) == Sat
  }

  private def isClearlyZeroPerm(t: Term): Boolean = {
    TermRewriter.simplify(t) match {
      case PermFracTerm(IntTerm(a), _) => {
        a.equals(BigInt.int2bigInt(0))
      }
      case _ => false
    }
  }

  def withMWM(manager: MagicWandManager): KnowledgeBase = {
    KnowledgeBase(
      this.path,
      this.assignment,
      this.heap,
      this.direct,
      this.folded,
      this.info,
      this.partial,
      manager,
      this.fieldTypes
    )

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

      // find applicable magic wands
      val applicable = this.mwm.wands.flatMap(w => {
          val alreadyInDirect = w.foldedCons.toSeq.filter(p => p.pred.equals(fa.pred))
          val inPartialKnowledge = w.partialCons.toSeq
            .filter(p => engine.provePure(this, p.prem) == Sat)
            .flatMap(p => PredicateCollector.collectFoldedPredicates(engine, p.cons, this))
            .flatMap(f => findUnfoldingStrategyInPredicate(engine, defs, fa, f))
          val selfInPartial = w.partialCons.toSeq
            .filter(p => engine.provePure(this, p.prem) == Sat)
            .flatMap(p => PredicateCollector.collectFoldedPredicates(engine, p.cons, this))
            .exists(f => f.pred.equals(fa.pred))
          val unfoldingStrats = w.foldedCons.toSeq.flatMap(f => findUnfoldingStrategyInPredicate(engine, defs, fa, f))
          val selfInFolded = w.foldedCons.exists(p => p.pred.equals(fa.pred))
          println(s"CHECKING -------- ${fa.pretty()}   IN    ${w.pretty()}    ${this.path}")
          println(s"in direct: ${alreadyInDirect.nonEmpty}")
          println(s"in partial: ${inPartialKnowledge.nonEmpty}")
          println(s"in unfolding: ${unfoldingStrats.nonEmpty}")
          println("CHECKING STOP -----")
          if (selfInFolded || selfInPartial || alreadyInDirect.nonEmpty || inPartialKnowledge.nonEmpty || unfoldingStrats.nonEmpty) {
            Some((w, Seq(ApplyStep(w, PermAmount.WRITE)) ++ inPartialKnowledge ++ unfoldingStrats))
          }
          else {
            None
          }
        })
        .filter(a => {
          val w = a._1
          val allDirects = w.directPrem.forall(p => {
            isNotZeroPerm(engine, this.direct.getAmount(p.exp))
          })
          val allFolded = w.foldedPrem.forall(p => {
            isNotZeroPerm(engine, this.folded.getAmount(p.pred))
          })
          allDirects && allFolded
        })
        .flatMap(a => a._2)
        .toSeq

      val strats = mapped.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, fa, v))
      if (applicable.nonEmpty || strats.nonEmpty) {
        Some(RefoldingStrategy(applicable ++ strats))
      }
      else {
        None
      }
    }
  }

  def findUnfoldingStrategyInBaguette(engine: ReasoningEngine, defs: Map[String, PredDef], mag: BaguetteMagic): Option[RefoldingStrategy] = {
    //    findUnfoldingStrategyInPredicate(engine, defs, )
    None
  }


  def findUnfoldingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], impl: ImplTerm): Option[RefoldingStrategy] = {
    // TODO: check if it is even possible that the permission amount is reachable
    if (this.partial.partial.contains(impl)) {
      Some(RefoldingStrategy(Seq()))
    }
    else {
      val mapped: Seq[PredInstAccTerm] = this.folded.permissions.map(e => PredInstAccTerm(e._1, e._2))
        .filter(i => !isClearlyZeroPerm(i.perm))
        .filter(i => isNotZeroPerm(engine, i.perm))
        .toSeq

      val strats = mapped.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, impl, v))
      if (strats.nonEmpty) {
        Some(RefoldingStrategy(strats))
      }
      else {
        None
      }
    }
  }


  def findUnfoldingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], fa: PredFieldAccTerm): Option[RefoldingStrategy] = {
    // TODO: check if it is even possible that the permission amount is reachable
    val directAmount = this.direct.getAmount(fa.exp)
    if (hasEnoughPermissions(engine, fa.perm, directAmount)) {
      Some(RefoldingStrategy(Seq()))
    }
    else {
      // find relevant folded permissions
      val mapped: Seq[PredInstAccTerm] = this.folded.permissions.map(e => PredInstAccTerm(e._1, e._2))
        .filter(i => !isClearlyZeroPerm(i.perm))
        .filter(i => isNotZeroPerm(engine, i.perm))
        .toSeq

      // find applicable magic wands
      val applicable = this.mwm.wands.flatMap(w => {
          val alreadyInDirect = w.directCons.map(_.exp).contains(fa.exp)
          val unfoldingStrats = w.foldedCons.toSeq.flatMap(f => findUnfoldingStrategyInPredicate(engine, defs, fa, f))
          // TODO: extend with partial knowledge
          if (alreadyInDirect || unfoldingStrats.nonEmpty) {
            Some((w, Seq(ApplyStep(w, PermAmount.WRITE)) ++ unfoldingStrats))
          }
          else {
            None
          }
        })
        .filter(a => {
          val w = a._1
          val allDirects = w.directPrem.forall(p => {
            isNotZeroPerm(engine, this.direct.getAmount(p.exp))
          })
          val allFolded = w.foldedPrem.forall(p => {
            isNotZeroPerm(engine, this.folded.getAmount(p.pred))
          })
          allDirects && allFolded
        })
        .flatMap(a => a._2)
        .toSeq

      val strats = mapped.flatMap(v => {
        println(s"FINDING UNFOLDING STRATEGY FOR ${fa.pretty()} IN ${v.pretty()}")
        val res = findUnfoldingStrategyInPredicate(engine, defs, fa, v)
        println(res)
        res
      })
      if (applicable.nonEmpty || strats.nonEmpty) {
        Some(RefoldingStrategy(applicable ++ strats))
      }
      else {
        None
      }
    }
  }

  def unfold(engine: ReasoningEngine, defs: Map[String, PredDef], pred: PredInst, perm: Term): KnowledgeBase = {
    val predDef = defs(pred.name)

    val instantiated = predDef.instantiate(pred)

    val (afterNorm, body) = TermNormalization.normalizeMutablePartsInLogicTerm(this, this, instantiated)

    val direct = PredicateCollector.collectDirectPredicates(engine, body, afterNorm)
    val folded = PredicateCollector.collectFoldedPredicates(engine, body, afterNorm)
    val partial = PredicateCollector.collectPotSatImpls(engine, body, afterNorm)
    val pure = PredicateCollector.stripToPure(engine, body, afterNorm)

    // TODO: NORMALIZE THE CONTENT OF THE PREDICATE OTHERWISE IT DOES NOT PARSE CORRECTLY

    // exhale the folded predicate amount
    val exhaled = afterNorm.update((a, h, d, f, i, p) => (a, h, d, f.exhale(pred, perm), i, p))

    // TODO: check for any knowledge where access has been lost and eliminate info
    //          ---> for inhale and exhale

    val up = exhaled.withPartial(this.partial.inhale(partial))
    val ui = up.withInfo(exhaled.info.and(pure))

    // inhale normalized amount
    val ud = direct
      .map(d => PredFieldAccTerm(d.exp, MulTerm(d.perm, perm)))
      .foldLeft(ui)((a, b) => {
        //        val (afterExpNorm, refE, typE, infoE) = TermNormalization.computeNormalizedValueRef(a, a.assignment.rc, b.exp.src)
        //        val (afterPermNorm, refP, typP, infoP) = TermNormalization.computeNormalizedValueRef(afterExpNorm, a.assignment.rc, b.perm)

        //        val varE = refE.toVarTerm(typE)
        //        val varP = refP.toVarTerm(typP)

        //        val uFA = PredFieldAccTerm(
        //          FieldAccTerm(varE, b.exp.field, b.exp.typ),
        //          varP
        //        )
        a.update((a, h, d, f, i, p) => {
          (a, h, d.inhale(b), f, i, p)
        })
      })

    val uf = folded
      .map(d => PredInstAccTerm(d.pred, MulTerm(d.perm, perm)))
      .foldLeft(ud)((a, b) => {
        //        val (afterExpNorm, args, infoE) = TermNormalization.computeNormalizedTermList(a, a.assignment.rc, b.pred.args)
        //        val (afterPermNorm, refP, typP, infoP) = TermNormalization.computeNormalizedValueRef(afterExpNorm, a.assignment.rc, b.perm)
        //
        //        val varP = refP.toVarTerm(typP)
        //
        //        val uFA = PredInstAccTerm(
        //          PredInst(b.pred.name, args),
        //          varP
        //        )
        //        afterPermNorm.update((a, h, d, f, i, p) => {
        //          (a, h, d, f.inhale(uFA), i.and(infoE).and(infoP), p)
        //        })
        a.update((a, h, d, f, i, p) => {
          (a, h, d, f.inhale(b), i, p)
        })
      })

    uf
  }

  def withPartial(potential: Potential): KnowledgeBase = {
    KnowledgeBase(this.path, this.assignment, this.heap, this.direct, this.folded, this.info, potential, this.mwm, this.fieldTypes)
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

    // todo: normalization of internals might lead to duplicate initialization of field temp variables
    val instantiated = predDef.instantiate(f.pred)

    val (afterNorm, normTerm) = TermNormalization.normalizeMutablePartsInLogicTerm(this, this, instantiated)

    val folded = PredicateCollector.collectFoldedPredicatesExtended(engine, normTerm, afterNorm)
    val direct = PredicateCollector.collectDirectPredicates(engine, normTerm, afterNorm)
    val stripped = PredicateCollector.stripToPure(engine, normTerm, afterNorm)
    val partial = PredicateCollector.collectPotSatImpls(engine, normTerm, afterNorm)
    val baguettes = PredicateCollector.collectBaguettes(engine, normTerm, afterNorm)

    println(s"CHECKING FOR PARTIAL IN THE REFOLDING STRATEGY:")
    println(f.pretty())
    partial.foreach(p => println(p.pretty()))

    println("CHECKING FOR FOLDED IN THE REFOLDING STRATEGY:")
    println(f.pretty())
    folded.foreach(p => println(p.pretty()))

    val mappedDirect = direct.map(d => afterNorm.findUnfoldingStrategy(engine, defs, d))
    val mappedFolded = folded.map(f => afterNorm.findRefoldingStrategy(engine, defs, f))
    val mappedPartial = partial.map(p => afterNorm.findUnfoldingStrategy(engine, defs, p))

    println(s"CHECKING FOR DIRECT REQUIREMENTS:")
    println(s"${direct.zip(mappedDirect).map(v => s"${v._1.pretty()}   =>  ${v._2}").mkString("\n").indent(2)}")

    mergeRefoldingStrategyOptions(mappedDirect ++ mappedFolded ++ mappedPartial)
      .map(r => RefoldingStrategy(r.steps ++ Seq(FoldingStep(f.pred, f.perm))))
  }

  def findRepackagingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], wand: BaguetteMagic): Option[RefoldingStrategy] = {
    println(s"Processing repackaging start: ${wand.pretty()}")
    // preparing the knowledge base to perform the packaging procedure
    val extendedWithDirect = wand.directPrem.foldLeft(this)((a, b) => {
      // create a fresh temp variable which represents the current permission amount for this field
      val rc = a.assignment.rc
      val current = a.direct.getAmount(b.exp)
      val res = rc.freshValRef().toVarTerm(Perm)

      // setting the current permission amount to a max of 1/1
      val conditioned = CondTerm(
        LessEqCmpTerm(AddTerm(b.perm, current), PermAmount.WRITE),
        AddTerm(b.perm, current),
        PermAmount.WRITE
      )

      // update the entry in the direct permission mask
      val dir = DirectPermissionMask(a.direct.permissions.updated(b.exp, res))

      // update the knowledge base
      a.withDirect(dir)
        .extendInfo(EqCmpTerm(res, conditioned))
    })

    val extendedWithFolded = wand.foldedPrem.foldLeft(extendedWithDirect)((a, b) => {
      // create a fresh temp variable which represents the current permission amount for this predicate
      val rc = a.assignment.rc
      val current = a.folded.getAmount(b.pred)
      val res = rc.freshValRef().toVarTerm(Perm)

      // setting the current permission amount to a max of 1/1
      val conditioned = CondTerm(
        LessEqCmpTerm(AddTerm(b.perm, current), PermAmount.WRITE),
        AddTerm(b.perm, current),
        PermAmount.WRITE
      )

      // update the entry in the direct permission mask
      val fol = FoldedPermissionMask(a.folded.permissions.updated(b.pred, res))

      // update the knowledge base
      a.withFolded(fol)
        .extendInfo(EqCmpTerm(res, conditioned))
    })

    // TODO: this guarding strategy does not work!!!!
    // -> cleaning with potential does not work just like that
    // -> it allows 2/1 permissions
    val extendedWithPartial = wand.partialPrem.foldLeft(extendedWithFolded)((a, b) => {
      a.withPartial(a.partial.inhale(Seq(b)))
    })

    val afterExtension = extendedWithPartial

    val afterCleaned = afterExtension.cleanPotentialWithCurrentKnowledge(engine)

    // finding a refolding strategy
    val (additionalDirect, additionalFolded) = wand.partialCons.foldLeft((Seq[PredFieldAccTerm](), Seq[PredInstAccTerm]()))((acc, d) => {
      val proofRes = engine.provePure(afterCleaned, d.prem)
      println(s"${d.prem.pretty()} has proof result: ${proofRes}")
      if (proofRes == Sat) {
        // anything else is assumed to not be contained
        val dirs = PredicateCollector.collectDirectPredicates(engine, d.cons, afterCleaned)
        val fols = PredicateCollector.collectFoldedPredicates(engine, d.cons, afterCleaned)
        println(s"DIRS: ${dirs}")
        println(s"FOLS: ${fols}")
        (acc._1 ++ dirs, acc._2 ++ fols)
      }
      else {
        // if the premise of this partial info is not satisfied then it is assumed to always hold
        (Seq(), Seq())
      }
    })

    println(s"ADDITIONAL DIRECT: ${}")
    println(additionalDirect.map(_.pretty()).mkString(" &&&& "))
    println(additionalFolded.map(_.pretty()).mkString(" &&&& "))

    println(LogicTermRewriting.untangle(afterCleaned).pretty())
    println(afterCleaned.pretty())


    val (kbDirect, directStrategies) = (wand.directCons ++ additionalDirect).foldLeft((afterCleaned, Seq[Option[RefoldingStrategy]]()))((acc, d) => {
      val strat = acc._1.findUnfoldingStrategy(engine, defs, d)
      val applied = strat.map(s => acc._1.applyRefoldingStrategy(engine, defs, s)).getOrElse(acc._1)
      (applied, acc._2 ++ Seq(strat))
    })

    val (_, foldedStrategies) = (wand.foldedCons ++ additionalFolded).foldLeft((kbDirect, Seq[Option[RefoldingStrategy]]()))((acc, d) => {
      val strat = acc._1.findRefoldingStrategy(engine, defs, d)
      val applied = strat.map(s => acc._1.applyRefoldingStrategy(engine, defs, s)).getOrElse(acc._1)
      (applied, acc._2 ++ Seq(strat))
    })

    directStrategies.foreach(a => println(a))
    foldedStrategies.foreach(a => println(a))


    val mergedStrategies = directStrategies ++ foldedStrategies

    val combined = mergedStrategies.foldLeft(Some(Seq()).asInstanceOf[Option[Seq[RefoldingStep]]])((c, s) => {
        c.flatMap(a => s.map(q => a ++ q.steps))
      })
      .map(s => RefoldingStrategy(Seq(PackageStep(wand, s))))

    println(s"Processing repackaging stop: ${wand.pretty()}")

    combined
  }

  def findRefoldingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], f: PredInstAccTerm): Option[RefoldingStrategy] = {
    /*
      when finding a refolding strategy first search for a typical refolding
      if nothing is found that way check if a magic wand application could solve this issue
    */

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

  def withDirect(direct: DirectPermissionMask): KnowledgeBase = {
    KnowledgeBase(
      this.path,
      this.assignment,
      this.heap,
      direct,
      this.folded,
      this.info,
      this.partial,
      this.mwm,
      this.fieldTypes
    )
  }

  def withFolded(folded: FoldedPermissionMask): KnowledgeBase = {
    KnowledgeBase(
      this.path,
      this.assignment,
      this.heap,
      this.direct,
      folded,
      this.info,
      this.partial,
      this.mwm,
      this.fieldTypes
    )
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
      this.mwm,
      this.fieldTypes
    )
  }

  def cleanPotentialWithCurrentKnowledge(engine: ReasoningEngine): KnowledgeBase = {
    // TODO: improve this to only invoke prover a single time
    val sat = this.partial.partial.filter(p => engine.provePureWithPotential(this, p.prem).equals(Sat))
      .map(p => p.cons)
    val unsat = this.partial.partial.filter(p => engine.provePureWithPotential(this, p.prem).equals(UnSat))
    val potsat = this.partial.partial.filter(p => engine.provePureWithPotential(this, p.prem).equals(PotSat))

    //    println("CLEANING PROGRAM:")
    //    println(s"SAT: ${sat.map(_.pretty())}")
    //    println(s"UNSAT: ${unsat.map(_.pretty())}")
    //    println(s"POTSAT: ${potsat.map(_.pretty())}")

    if (sat.isEmpty && unsat.isEmpty) {
      this
    }
    else {
      val redPot = this.update((a, h, d, f, i, _) => (a, h, d, f, i, Potential(potsat)))
      sat.foldLeft(redPot)((kb, r) => {
        val dirs = PredicateCollector.collectDirectPredicates(engine, r, kb)
        val folds = PredicateCollector.collectFoldedPredicates(engine, r, kb)
        val pots = PredicateCollector.collectPotSatImpls(engine, r, kb)
        val pure = PredicateCollector.stripToPure(engine, r, kb)
        kb.update((a, h, d, f, i, p) => {
          val ud = dirs.foldLeft(d)((a, b) => a.inhale(b))
          val uf = folds.foldLeft(f)((a, b) => a.inhale(b))
          val ui = i.and(pure)
          val up = p.inhale(pots)
          (a, h, ud, uf, ui, up)
        })
      })
    }
  }

  private def applyRefoldingStep(engine: ReasoningEngine, defs: Map[String, PredDef], base: KnowledgeBase, step: RefoldingStep): KnowledgeBase = {
    step match {
      case FoldingStep(pred, perm) => {
        // if in the future the folding step has sub steps to fold other stuff beforehand then
        // insert the folding here before folding self

        // fold self
        base.fold(engine, defs, pred, perm)
      }
      case UnfoldingStep(pred, perm, subs) => {
        // unfold the predicate on the current level
        val unfolded = base.unfold(engine, defs, pred, perm)
        // unfold all the steps within this predicate
        // the substeps are scaled by the amount that the current unfolding actually unfolded
        subs.map(s => s.scale(perm))
          .foldLeft(unfolded)((a, b) => applyRefoldingStep(engine, defs, a, b))
      }
      case PackageStep(wand, steps) => {
        println(s"Processing: ${wand.pretty()}")
        // preparing the knowledge base to perform the packaging procedure
        val extendedWithDirect = wand.directPrem.foldLeft(base)((a, b) => {
          // create a fresh temp variable which represents the current permission amount for this field
          val rc = a.assignment.rc
          val current = a.direct.getAmount(b.exp)
          val res = rc.freshValRef().toVarTerm(Perm)

          // setting the current permission amount to a max of 1/1
          val conditioned = CondTerm(
            LessEqCmpTerm(AddTerm(b.perm, current), PermAmount.WRITE),
            AddTerm(b.perm, current),
            PermAmount.WRITE
          )

          // update the entry in the direct permission mask
          val dir = DirectPermissionMask(a.direct.permissions.updated(b.exp, res))

          // update the knowledge base
          a.withDirect(dir)
            .extendInfo(EqCmpTerm(res, conditioned))
        })

        val extendedWithFolded = wand.foldedPrem.foldLeft(extendedWithDirect)((a, b) => {
          // create a fresh temp variable which represents the current permission amount for this predicate
          val rc = a.assignment.rc
          val current = a.folded.getAmount(b.pred)
          val res = rc.freshValRef().toVarTerm(Perm)

          // setting the current permission amount to a max of 1/1
          val conditioned = CondTerm(
            LessEqCmpTerm(AddTerm(b.perm, current), PermAmount.WRITE),
            AddTerm(b.perm, current),
            PermAmount.WRITE
          )

          // update the entry in the direct permission mask
          val fol = FoldedPermissionMask(a.folded.permissions.updated(b.pred, res))

          // update the knowledge base
          a.withFolded(fol)
            .extendInfo(EqCmpTerm(res, conditioned))
        })

        //        println("EXTENDED WITH DIRECT STUFF:")
        //        println(extendedWithFolded.pretty())

        // applying the steps of the packaging procedure
        val afterSteps = steps.foldLeft(extendedWithFolded)((k, s) => applyRefoldingStep(engine, defs, k, s))
        //        println("AFTER STEPS:")
        //        println(afterSteps.pretty())

        // exhaling the permissions which are the consequence of the magic wand
        val exhaledDirect = wand.directCons.foldLeft(afterSteps)((k, d) => k.withDirect(k.direct.exhale(d)))
        val exhaledFolded = wand.foldedCons.foldLeft(exhaledDirect)((k, d) => k.withFolded(k.folded.exhale(d)))

        //        println("AFTER EXHALING RESULT:")
        //        println(exhaledFolded.pretty())

        // adding the magic wand to the current context
        val inhalingWand = exhaledFolded.withMWM(exhaledFolded.mwm.addWand(wand))

        //        println("AFTER INHALING WAND:")
        //        println(inhalingWand.pretty())

        // reconstruction of remaining permissions after performing the folding operations
        val dirKeys = wand.directPrem.map(d => d.exp)
          .union(wand.directCons.map(d => d.exp))
          .union(base.direct.permissions.keySet)
          .union(extendedWithDirect.direct.permissions.keySet)
          .union(inhalingWand.direct.permissions.keySet)

        val foldedKeys = wand.foldedPrem.map(d => d.pred)
          .union(wand.foldedCons.map(d => d.pred))
          .union(base.folded.permissions.keySet)
          .union(extendedWithDirect.folded.permissions.keySet)
          .union(inhalingWand.folded.permissions.keySet)

        val adjustedDirects = dirKeys.foldLeft(inhalingWand)((k, d) => {
          // currently hypothetical formula:
          // used amount = before packaging - after packaging
          // adjusted = provided - (used - prem)

          // determine the amount that is provided before the packaging step
          val provided = base.direct.getAmount(d)
          // determine the amount used by the folding procedure
          val before = extendedWithFolded.direct.getAmount(d)
          val after = inhalingWand.direct.getAmount(d)
          val used = SubTerm(before, after)

          // determine the amount that is specified in the premise of the magic wand
          val prem = wand.directPrem.filter(p => p.exp.equals(d))
            .map(d => d.perm)
            .reduceLeftOption(AddTerm)
            .getOrElse(PermAmount.NONE)

          // prevent unfolding internally to influence the outside permission value
          val conditioned = CondTerm(
            LessEqCmpTerm(SubTerm(used, prem), PermAmount.NONE),
            PermAmount.NONE,
            SubTerm(used, prem)
          )

          // compute the adjusted amount using the given hypothetical formula
          val adjusted = SubTerm(provided, conditioned)

          //          println(s"SIMP ADJUSTED   ${d.pretty()}: ${TermRewriter.simplify(adjusted).pretty()}")

          k.withDirect(DirectPermissionMask(k.direct.permissions.updated(d, adjusted)))
        })

        val adjustedFolded = foldedKeys.foldLeft(adjustedDirects)((k, d) => {
          // before = base + prem >= 1/1 ? 1/1 : base + prem
          // used = before - after
          // adjusted = provided - (used - prem <= 0/1 ? 0/1 : used - prem)

          // determine the amount that is provided before the packaging step
          val provided = base.folded.getAmount(d)
          // determine the amount used by the folding procedure
          val before = extendedWithFolded.folded.getAmount(d)
          val after = inhalingWand.folded.getAmount(d)
          val used = SubTerm(before, after)

          // determine the amount that is specified in the premise of the magic wand
          val prem = wand.foldedPrem.filter(p => p.pred.equals(d))
            .map(d => d.perm)
            .reduceLeftOption(AddTerm)
            .getOrElse(PermAmount.NONE)

          // prevent unfolding internally to influence the outside permission value
          val conditioned = CondTerm(
            LessEqCmpTerm(SubTerm(used, prem), PermAmount.NONE),
            PermAmount.NONE,
            SubTerm(used, prem)
          )

          // compute the adjusted amount using the given hypothetical formula
          val adjusted = SubTerm(provided, conditioned)

          //          println(s"SIMP ADJUSTED   ${d.pretty()}: ${TermRewriter.simplify(adjusted).pretty()}")

          k.withFolded(FoldedPermissionMask(k.folded.permissions.updated(d, adjusted)))
        })

        //        println("AFTER ADJUSTING REMAINING PERMISSIONS:")
        //        println(adjustedFolded.pretty())

        adjustedFolded
      }
      case ApplyStep(wand, perm) => {
        //        println(s"APPLYING MW: ${wand.pretty()}")
        // exhale the premise of the magic wand
        val exDirPrem = wand.directPrem.foldLeft(base)((k, d) => {
          val scaled = PredFieldAccTerm(d.exp, MulTerm(d.perm, perm))
          k.withDirect(k.direct.exhale(scaled))
        })
        val exFolPrem = wand.foldedPrem.foldLeft(exDirPrem)((k, f) => {
          val scaled = PredInstAccTerm(f.pred, MulTerm(f.perm, perm))
          k.withFolded(k.folded.exhale(scaled))
        })

        // inhale the consequence of the magic wand
        val inDirCons = wand.directCons.foldLeft(exFolPrem)((k, f) => {
          val scaled = PredFieldAccTerm(f.exp, MulTerm(f.perm, perm))
          k.withDirect(k.direct.inhale(scaled))
        })
        val inFolCons = wand.foldedCons.foldLeft(inDirCons)((k, f) => {
          val scaled = PredInstAccTerm(f.pred, MulTerm(f.perm, perm))
          k.withFolded(k.folded.inhale(scaled))
        })

        // remove the magic wand from the
        val remWand = inFolCons.withMWM(inFolCons.mwm.removeWand(wand))

        //        println("AFTER APPLYING MW:")
        //        println(remWand.pretty())

        remWand
      }
      case c => {
        throw new IllegalArgumentException(s"Unable to process refolding step type ${c.getClass.getCanonicalName}")
      }
    }
  }

  def applyRefoldingStrategy(engine: ReasoningEngine, defs: Map[String, PredDef], refolding: RefoldingStrategy): KnowledgeBase = {
    refolding.steps.foldLeft(this)((a, b) => applyRefoldingStep(engine, defs, a, b))
  }
}


/*

  statt related work: background chapter

  formal problem statement section (unsoundness ist related)

  examples sollte es zwischendurch immer eingestreut geben
  evaluation später als extra kapitel

  reihenfolge neu/korrekt ordnen
  nach dem problem statement die algorithmus pipeline vorstellen

  template runterladen: acm small format

  ich suche eine verallgemeinerung für die call sites und die constraints suchen

  globale analyse die nach allen methoden inferences schaut wie die benutzt werden
  - generate lemmas that prove the:

  write permissions überall fordern
  mit magic wands arbeiten


*/


/*

get(l: List, idx: Int)

-> Implicitly walking in parallel with list transformed into integer using `length` function
       l  = Cons(e1, Cons(e2  Cons(e3  r)))
length(l) = Succ(    Succ(    Succ(    n)))

As long as 0 <= idx < length(l) the successor always exists inside the list

In other words its:
get(len: Int, i: Int)
  i == 0 => len = length(l) - idx
  i > 0 => len > 0
  i < 0 ==> ERROR unable to compare to nat







 */