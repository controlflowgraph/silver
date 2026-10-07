package viper.silver.inference.v3

import viper.silver.ast._
import viper.silver.inference.v3.ast._
import viper.silver.inference.v3.knowledge._
import viper.silver.verifier.Verifier

import scala.collection.mutable

trait Requirement {

}

case class IsNonNull(ref: ValRef) extends Requirement {

}

case class IsNull(ref: ValRef) extends Requirement {

}

case class HasFieldAcc(fa: FieldAccTerm, write: Boolean) extends Requirement {

}

case class HasPredInstAcc(fa: PredInstAccTerm, write: Boolean) extends Requirement {

}

trait Knowledge {

}

trait AdjustmentResponse[T] {}

case class SuccessfulAdjustment[T]() extends AdjustmentResponse[T] {}

case class FailedAdjustment[T]() extends AdjustmentResponse[T] {}

// TODO: when passing and adjusting the terms in branches the branchline does not provide the correect required "before" knowledge bases for each branch
case class ContinueAdjustment[T](cont: T) extends AdjustmentResponse[T] {}


case class LinePropagator[T](f: (Line, T) => AdjustmentResponse[T], ltt: T => LogicTerm) {
  def apply(l: Line, payload: T): AdjustmentResponse[T] = {
    this.f(l, payload)
  }

  def toLT(payload: T): LogicTerm = this.ltt(payload)
}

case class MethodInference(engine: ReasoningEngine,
                           defs: Map[String, PredDef], reps: Map[String, InternalMethod], currentMethod: InternalMethod,
                           knowledge: mutable.HashMap[Ident, Map[Seq[Term], KnowledgeBase]],
                           methSpec: mutable.HashMap[String, (Seq[LogicTerm], Seq[LogicTerm])],
                           injections: mutable.HashMap[Injection, Seq[RefoldingStrategy]]) {

  def attemptMagicWandConstruction(kb: KnowledgeBase, variable: VarTerm, pred: PredInstAccTerm): Option[(BaguetteMagic, RefoldingStrategy)] = {
    println(s"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  ${pred.pretty()}  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% ${kb.path.map(_._2)}")
    val predDef = this.defs(pred.pred.name)
    val predBody = predDef.instantiate(pred.pred)
    // locate the stuff that is not satisfied yet

    // TODO: maybe extend with pure parts
    val (afterNorm, normTerm) = TermNormalization.normalizeMutablePartsInLogicTerm(kb, kb, predBody)
    val folded = PredicateCollector.collectFoldedPredicates(this.engine, normTerm, kb)
    val direct = PredicateCollector.collectDirectPredicates(this.engine, normTerm, kb)
    //    val rawStripped = PredicateCollector.stripToPure(this.engine, normTerm, kb)
    val partial = PredicateCollector.collectPotSatImpls(this.engine, normTerm, kb)

    println(s"Folded Requirements: ${folded.map(_.pretty()).mkString("   &   ")}")
    println(s"Direct Requirements: ${direct.map(_.pretty()).mkString("   &   ")}")
    println(s"Partial Requirements: ${partial.map(_.pretty()).mkString("   &   ")}")
    println("Knowledge Base:")
    println(afterNorm.pretty())
    //    val (afterNorm, stripped) = normalizeLogicTerm(kb2, rawStripped)
    //    val (kb4, partial) = normalizePotentialRequirements(afterNorm, rawPartial)

    //    println("CHECKING FOLDED:")
    val foldedStrategies = folded.map(f => (f, afterNorm.findRefoldingStrategy(this.engine, this.defs, f)))
    val missingFolded = foldedStrategies.filter(f => f._2.isEmpty).map(d => d._1)
    val directStrategies = direct.map(d => (d, afterNorm.findUnfoldingStrategy(this.engine, this.defs, d)))
    val missingDirect = directStrategies.filter(d => d._2.isEmpty).map(d => d._1)
    val partialStrategies = partial.map(d => (d, !(afterNorm.partial.partial.contains(d))))
    val missingPartial = partialStrategies.filter(d => d._2).map(d => d._1)

    println(s"missing folded: ${missingFolded.map(_.pretty()).mkString(" & ")}")
    println(s"missing direct: ${missingDirect.map(_.pretty()).mkString(" & ")}")
    println(s"missing partial: ${missingPartial.map(_.pretty()).mkString(" & ")}")
    println("")
    val bmI = afterNorm.constructInfoBackMapping()
    val bmH = afterNorm.constructBackMapping(this.currentMethod, useAllVariables = true)
    val bm = bmH.followedBy(bmI)
    println(s"missing folded bm: ${missingFolded.map(v => applyBm(bm, v)).map(_.pretty()).mkString(" & ")}")
    println(s"missing direct bm: ${missingDirect.map(v => applyBm(bm, v)).map(_.pretty()).mkString(" & ")}")
    println(s"missing partial bm: ${missingPartial.map(v => applyBm(bm, v)).map(_.pretty()).mkString(" & ")}")
    println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%")

    val notAllContentMissing = folded.size != missingFolded.size || direct.size != missingDirect.size || partial.size != missingPartial.size

    if (notAllContentMissing) {
      val merged = missingDirect ++ missingFolded ++ missingPartial
      val folStrat = foldedStrategies.filter(d => d._2.nonEmpty).flatMap(d => d._2)
      val dirStrat = directStrategies.filter(d => d._2.nonEmpty).flatMap(d => d._2)
      val combined = (folStrat ++ dirStrat).flatMap(d => d.steps)
      val additional = Seq(
        FoldingStep(pred.pred, pred.perm)
      )
      val wand = BaguetteMagic(missingDirect.toSet, missingFolded.toSet, missingPartial.toSet, Set(), Set(), Set(ImplTerm(NotEqCmpTerm(variable, NullTerm()), pred)))
      val packaging = PackageStep(wand, combined ++ additional)
      println(packaging.pretty())
      println(s"ALLOWING MAGIC WAND: (${merged.map(_.pretty()).mkString(" && ")}) --* (${pred.pretty()})")
      Some((wand, RefoldingStrategy(Seq(packaging))))
    }
    else {
      None
    }
  }

  def collectRequiredFieldPermissions(term: Term): Set[PredFieldAccTerm] = {
    term match {
      case AddTerm(a, b) => {
        val reqA = collectRequiredFieldPermissions(a)
        val reqB = collectRequiredFieldPermissions(b)
        reqA.union(reqB)
      }
      case MulTerm(a, b) => {
        val reqA = collectRequiredFieldPermissions(a)
        val reqB = collectRequiredFieldPermissions(b)
        reqA.union(reqB)
      }
      case fa@FieldAccTerm(src, _, _) => {
        val recS = collectRequiredFieldPermissions(src)
        // this assumes that the value is taken via
        recS.union(Set(PredFieldAccTerm(fa, PermFracTerm(IntTerm(1), IntTerm(2)))))
      }
      case _: IntTerm => Set()
      case _: BoolTerm => Set()
      case AndTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case EqCmpTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case GreaterCmpTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case GreaterEqCmpTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case ImplTerm(prem, cons) => collectRequiredFieldPermissions(prem).union(collectRequiredFieldPermissions(cons))
      case LessCmpTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case LessEqCmpTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case NotEqCmpTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case NotTerm(t) => collectRequiredFieldPermissions(t)
      case OrTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case PredFieldAccTerm(_, perm) => collectRequiredFieldPermissions(perm)
      case PredInstAccTerm(_, perm) => collectRequiredFieldPermissions(perm)
      case _: VarTerm => Set()
      case NegTerm(t) => collectRequiredFieldPermissions(t)
      case NullTerm() => Set()
      case PermFracTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case SubTerm(a, b) => collectRequiredFieldPermissions(a).union(collectRequiredFieldPermissions(b))
      case c => {
        throw new IllegalArgumentException(s"Unable to extract required permissions from term type: ${term.getClass.getCanonicalName}")
      }
    }
  }


  private def applyRefoldingStrategy(engine: ReasoningEngine, inj: Injection, before: KnowledgeBase, strat: RefoldingStrategy): KnowledgeBase = {
    val bm = before.constructBackMapping(this.currentMethod, useAllVariables = true)
    val infoBm = before.constructInfoBackMapping()
    val ts = bm.followedBy(infoBm)
    val rewritten = FixedPoint.compute(strat, (s: RefoldingStrategy) => {
      s.rewrite(ts)
    })
    addRefoldingStrategiesToInjectionPoint(inj, Seq(rewritten))
    before.applyRefoldingStrategy(engine, this.defs, strat)
  }

  private def applyStrategies(engine: ReasoningEngine, inj: Injection, before: KnowledgeBase, strats: Seq[RefoldingStrategy]): KnowledgeBase = {
    strats.foldLeft(before)((kb, s) => applyRefoldingStrategy(engine, inj, kb, s))
  }

  private def propagateBackFieldPermReq(from: Ident, pred: PredFieldAccTerm, actual: Term): Boolean = {
    // TODO: fix the shortcut and actually propagate the requirements backward
    println(s"PROPAGATING BACK FIELD PERM: ${pred.pretty()} has only ${actual.pretty()} from ${from}")
    val currentSpec = this.methSpec(this.currentMethod.method)
    val currentPre = currentSpec._1
    val currentPost = currentSpec._2
    val remainingRequired = TermRewriter.simplify(SubTerm(pred.perm, actual))
    this.methSpec.put(this.currentMethod.method, (currentPre ++ Seq(PredFieldAccTerm(pred.exp, remainingRequired)), currentPost))

    true
  }

  private def getRefoldingStrategiesAtInjectionPoint(inj: Injection): Seq[RefoldingStrategy] = {
    this.injections.getOrElse(inj, Seq())
  }

  private def clearInjection(inj: Injection): Unit = {
    this.injections.put(inj, Seq())
  }

  private def addRefoldingStrategiesToInjectionPoint(inj: Injection, strat: Seq[RefoldingStrategy]): Unit = {
    val ext = getRefoldingStrategiesAtInjectionPoint(inj) ++ strat
    this.injections.put(inj, ext)
  }

  def mergeMappings(a: Map[Term, Term], b: Map[Term, Term]): Map[Term, Term] = {
    (a.toSeq ++ b.toSeq).toMap
  }

  def collectReplacements(lt: LogicTerm): Map[Term, Term] = {
    lt match {
      case AndTerm(a, b) => mergeMappings(collectReplacements(a), collectReplacements(b))
      case _: BoolTerm => Map()
      case EqCmpTerm(a@VarTerm(name, _), b) if (name.startsWith("t$")) => Seq(a -> b).toMap
      case _: EqCmpTerm => Map()
      case _: ImplTerm => Map()
      case _: GreaterCmpTerm => Map()
      case _: GreaterEqCmpTerm => Map()
      case _: LessCmpTerm => Map()
      case _: LessEqCmpTerm => Map()
      case _: NotEqCmpTerm => Map()
      case _: NotTerm => Map()
      case _: OrTerm => Map()
      case _: PredFieldAccTerm => Map()
      case _: PredInstAccTerm => Map()
      case _: VarTerm => Map()
      case c => {
        throw new IllegalArgumentException(s"Unable to collect replacements of logic term of type: ${c.getClass.getCanonicalName}")
      }
    }
  }

  def reconstructTerm(kb: KnowledgeBase, term: Term): Term = {
    // TODO: maybe two stage fix point
    //       -> first replace temps afap
    //       -> replace rest with assignment
    //       -> might not resolve all variables due to reassignment -> would get resolved further in previous parts of the code with different assignment
    //       => as long as there are temp variables in the formula it can not be applied to the specification?!?!?!?!?!?!?


    // when propagating back the reconstruction with the assignment should probably only happen right before adding to a specific method spec
    // before that it could lead to having wrong substitutions when reassigning a value earlier on
    // (or maybe not being able to traverse fully back to variables that make sense in the context of the specification)
    val mapping: Map[Term, Term] = kb.assignment.variables.map(a => a._2._1.toVarTerm(a._2._2) -> VarTerm(a._1, a._2._2)).toMap
    val replacements = collectReplacements(kb.info)
    val merged = mergeMappings(mapping, replacements)
    val ts = MapTermSub(merged)
    val f = ((t: Term) => t.substitute(ts))
    FixedPoint.compute(term, f)
  }

  private def searchForPermissionFieldAdjustmentToGetPermissions(kb: KnowledgeBase, fa: PredFieldAccTerm, already: Term): Unit = {
    val bmH = kb.constructBackMapping(this.currentMethod, useAllVariables = true)
    val bmI = kb.constructInfoBackMapping()
    val bm = bmH.followedBy(bmI)
    val bmFA = FixedPoint.compute(fa, (t: Term) => t.substitute(bm))
    val bmPerm = FixedPoint.compute(already, (t: Term) => t.substitute(bm))
    println(s"back mapped field access: ${bmFA.pretty()}")
    println(s"back mapped existing permission: ${bmPerm.pretty()}")
    // TODO: search in folded predicates for this field and unfold if possible
    // TODO: potentially propagate a constraint for the
  }

  def processRequirements(ln: Ident, inj: Injection, before: KnowledgeBase, directs: Set[PredFieldAccTerm], folded: Set[PredInstAccTerm], baguettes: Set[BaguetteMagic]): (Boolean, KnowledgeBase) = {
    val kbUnfoldingDirect = directs.foldLeft(before)((k, r) => {
      val strat = k.findUnfoldingStrategy(this.engine, this.defs, r)
      strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
    })

    val kbRefoldingFolded = folded.foldLeft(kbUnfoldingDirect)((k, r) => {
      val strat = k.findRefoldingStrategy(this.engine, this.defs, r)
      strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
    })

    val kbRefoldingBaguette = baguettes.foldLeft(kbUnfoldingDirect)((k, r) => {
      val strat = k.findRepackagingStrategy(this.engine, this.defs, r)
      strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
    })

    val kb = kbRefoldingBaguette

    // TODO: maybe rework this when there are equivalent objects that are separate in the heap
    val stillMissingDirect = directs.map(p => (p, kb.direct.getAmount(p.exp)))
      .filter(p => !kb.hasEnoughPermissions(this.engine, p._1.perm, p._2))

    // TODO: FIX THIS
    val stillMissingFolded = folded.map(p => (p, kb.folded.getAmount(p.pred)))
      .filter(p => !kb.hasEnoughPermissions(this.engine, p._1.perm, p._2))

    if (stillMissingDirect.isEmpty && stillMissingFolded.isEmpty) {
      (false, kb)
    }
    else {

      //      val relevantWandsDirect = kb.mwm.wands.filter(w => w.directCons.intersect(stillMissingDirect.map(_._1).nonEmpty))


      val someSuccessWithPotential = stillMissingDirect.map(a => findIfPotHasSolution(ln, kb, a._1, a._2))
        .exists(a => a)

      if (someSuccessWithPotential) {
        (true, kb)
      }
      else {

        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        println(s"BEFORE BACK PROP:")
        println(kb.pretty())
        stillMissingDirect.foreach(d => println(s"${d._1.pretty()}    proj has     ${d._2.pretty()}"))
        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")

        val someSuccessWithDirectPropVal = stillMissingDirect.map(p => propagateBackFieldPermReq(ln, p._1, p._2))
          .exists(a => a)
        if (someSuccessWithDirectPropVal) {
          (true, kb)
        }
        else {
          // TODO: fix when successful
          (false, kb)
        }
      }
    }


  }


  def processRequirements(ln: Ident, inj: Injection, before: KnowledgeBase, directs: Set[PredFieldAccTerm], folded: Set[PredInstAccTerm]): (Boolean, KnowledgeBase) = {
    val kbUnfoldingDirect = directs.foldLeft(before)((k, r) => {
      val strat = k.findUnfoldingStrategy(this.engine, this.defs, r)
      strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
    })

    val kbRefoldingFolded = folded.foldLeft(kbUnfoldingDirect)((k, r) => {
      val strat = k.findRefoldingStrategy(this.engine, this.defs, r)
      strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
    })

    val kb = kbRefoldingFolded

    // TODO: maybe rework this when there are equivalent objects that are separate in the heap
    val stillMissingDirect = directs.map(p => (p, kb.direct.getAmount(p.exp)))
      .filter(p => !kb.hasEnoughPermissions(this.engine, p._1.perm, p._2))

    // TODO: FIX THIS
    val stillMissingFolded = folded.map(p => (p, kb.folded.getAmount(p.pred)))
      .filter(p => !kb.hasEnoughPermissions(this.engine, p._1.perm, p._2))

    if (stillMissingDirect.isEmpty && stillMissingFolded.isEmpty) {
      (false, kb)
    }
    else {

      //      val relevantWandsDirect = kb.mwm.wands.filter(w => w.directCons.intersect(stillMissingDirect.map(_._1).nonEmpty))


      val someSuccessWithPotential = stillMissingDirect.map(a => findIfPotHasSolution(ln, kb, a._1, a._2))
        .exists(a => a)

      if (someSuccessWithPotential) {
        (true, kb)
      }
      else {

        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        println(s"BEFORE BACK PROP:")
        println(kb.pretty())
        stillMissingDirect.foreach(d => println(s"${d._1.pretty()}    proj has     ${d._2.pretty()}"))
        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")
        println("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$")

        val someSuccessWithDirectPropVal = stillMissingDirect.map(p => propagateBackFieldPermReq(ln, p._1, p._2))
          .exists(a => a)
        if (someSuccessWithDirectPropVal) {
          (true, kb)
        }
        else {
          // TODO: fix when successful
          (false, kb)
        }
      }
    }


  }

  private def havocPassedFragment(kb: KnowledgeBase): KnowledgeBase = {
    val retained = computeRetainedFragment(kb)
    val heap = Heap(
      kb.heap.rc,
      kb.heap.initialized,
      kb.heap.objMap.keys.foldLeft(Map[ValRef, Obj]())((m, k) => {
        val updatedFields = kb.heap.objMap(k).fields.foldLeft(Map[String, ValRef]())((r, f) => {
          if (retained.contains(k) && retained(k).contains(f._1)) {
            r.updated(f._1, f._2)
          }
          else {
            r.updated(f._1, kb.heap.rc.freshValRef())
          }
        })
        m.updated(k, Obj(k, updatedFields))
      }))
    kb.withHeap(heap)
  }

  private def computeRetainedFragment(kb: KnowledgeBase): Map[ValRef, Seq[String]] = {
    val allowedTransitions = kb.heap.objMap.values
      .flatMap(o => {
        val base = o.ref.toVarTerm(Ref)
        o.fields
          .toSeq
          .filter(f => {

            val fa = FieldAccTerm(base, f._1, kb.fieldTypes(f._1))
            val one = PermFracTerm(IntTerm(BigInt.int2bigInt(0)), IntTerm(BigInt.int2bigInt(1)))

            val strat = kb.findUnfoldingStrategy(this.engine, this.defs, PredFieldAccTerm(fa, one))
            val afterUnfold = strat.map(s => applyStrategies(this.engine, null, kb, Seq(s))).getOrElse(kb)

            val current = afterUnfold.direct.getAmount(fa)
            val zero = PermFracTerm(IntTerm(BigInt.int2bigInt(0)), IntTerm(BigInt.int2bigInt(1)))
            val check = GreaterCmpTerm(current, zero)

            val result = this.engine.provePure(afterUnfold, check)
            println(s"passed check: ${fa.pretty()}: ${result == Sat}")
            result == Sat
          })
          .map(f => (o.ref, f._1))
      })

    //    println("ALLOWED TRANSITIONS:")
    //    println(allowedTransitions.map(a => s"${a}").mkString("\n"))
    allowedTransitions.groupMap(a => a._1)(a => a._2).map(e => (e._1, e._2.toSeq))
  }

  private def processBranchLine(before: KnowledgeBase, bl: BranchLine): (Boolean, KnowledgeBase) = {
    val BranchLine(ln, pre, cond, thn, els) = bl
    // collecting the fields that are accessed within this
    val rawAccessPermissions = collectRequiredFieldPermissions(cond)
    val (normFields, accessPermissions) = TermNormalization.normalizeDirectRequirements(before, rawAccessPermissions.toSeq)

    val res = processRequirements(ln, pre, normFields, accessPermissions.toSet, Set())
    println("AFTER BRANCH LINE: ")
    println(res._2.pretty())
    res
  }

  private def processMergeLine(before: KnowledgeBase, ml: MergeLine): (Boolean, KnowledgeBase) = {
    (false, before)
  }

  private def processAssertLine(before: KnowledgeBase, al: AssertLine): (Boolean, KnowledgeBase) = {
    val AssertLine(ln, inj, exp) = al
    clearInjection(inj)

    // collecting the fields that are accessed within this
    val rawAccessPermissions = collectRequiredFieldPermissions(exp)
    val (normFields, accessPermissions) = TermNormalization.normalizeDirectRequirements(before, rawAccessPermissions.toSeq)

    val refolding = accessPermissions.foldLeft(normFields)((kb, d) => {
      kb.findUnfoldingStrategy(this.engine, this.defs, d)
        .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
        .getOrElse(kb)
    })

    //        println("REFOLDING KNOWLEDGE BASE:")
    //        println(refolding.pretty())

    val stillMissingFA = accessPermissions.map(p => (p, refolding.direct.getAmount(p.exp)))
      .filter(p => {
        val recP1 = reconstructTerm(refolding, p._1.perm)
        val recP2 = reconstructTerm(refolding, p._2)
        println(s"RECONSTRUCTION RESULT: ${p._1.pretty()}    ${p._2.pretty()}")
        println(recP1.pretty())
        println(recP2.pretty())
        !refolding.hasEnoughPermissions(this.engine, p._1.perm, p._2)
      })

    val someSuccessWithPotential = stillMissingFA.map(a => findIfPotHasSolution(ln, refolding, a._1, a._2))
      .exists(a => a)

    if (someSuccessWithPotential) {
      (true, refolding)
    }
    else {
      println(s"STILL MISSING THE ACCESS RIGHTS FOR: ${stillMissingFA.map(c => c._1.pretty() + "  " + c._2.pretty())}")
      val rawFolded = PredicateCollector.collectFoldedPredicates(this.engine, exp, refolding)
      val rawDirect = PredicateCollector.collectDirectPredicates(this.engine, exp, refolding)
      val rawStripped = PredicateCollector.stripToPure(this.engine, exp, refolding)
      val rawPartial = PredicateCollector.collectPotSatImpls(this.engine, exp, refolding)

      val (kb1, folded) = TermNormalization.normalizeFoldedRequirements(refolding, rawFolded)
      val (kb2, direct) = TermNormalization.normalizeDirectRequirements(kb1, rawDirect)
      val (kb3, stripped) = TermNormalization.normalizeLogicTerm(kb2, rawStripped)
      val (kb4, partial) = TermNormalization.normalizePotentialRequirements(kb3, rawPartial)

      println(s"RAW DIRECT: ${rawDirect}")
      println(s"NORMED DIRECT: ${direct}")

      direct.foreach(d => {
        println(s"::::::::::::::::::::::::::::::::::::::")
        println(s"CHECKING FRO DIRECT PREDICATE EXISTENCE: ${d}")
        this.engine.proveWithPotential(kb4, d)
        println(s"::::::::::::::::::::::::::::::::::::::")
      })

      println(s"::::::::::::::::::::::::::::::::::::::")
      println(s"CHECKING FOR STRIPPED: ${stripped.pretty()}")
      this.engine.proveWithPotential(kb4, stripped)
      println(s"::::::::::::::::::::::::::::::::::::::")


      val afterUnfolding = direct.foldLeft(kb4)((kb, d) => {
        kb.findUnfoldingStrategy(this.engine, this.defs, d)
          .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
          .getOrElse(kb)
      })

      val afterRefolding = folded.foldLeft(afterUnfolding)((kb, f) => {
        kb.findRefoldingStrategy(this.engine, this.defs, f)
          .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
          .getOrElse(kb)
      })

      (false, afterRefolding)
    }
  }

  private def processAssumeLine(before: KnowledgeBase, line: AssumeLine): (Boolean, KnowledgeBase) = {
    val AssumeLine(ln, exp) = line
    val stripped = PredicateCollector.stripToPure(this.engine, exp, before)
    val resKb = before.update(a => h => d => f => i => {
      (a, h, d, f, i.and(stripped))
    })
    val cleanedKb = resKb.cleanPotentialWithCurrentKnowledge(this.engine)
    (false, cleanedKb)
  }

  private def processCallLine(before: KnowledgeBase, line: CallLine): (Boolean, KnowledgeBase) = {
    val CallLine(ln, inj, method, targets, args) = line
    // TODO: include framing rule by checking if field access is retained
    val initial = this.reps(method)
    val spec = this.methSpec(method)

    val calledMethod = this.reps(method)

    val (afterArgNormalization, normArgs) = TermNormalization.normalizeMutablePartsInTermList(before, before, args)

    val substitution = MapTermSub(calledMethod.args.map(v => VarTerm(v._1, v._2)).zip(normArgs).toMap)

    // exhale the pres in reverse order
    val extendedPres = (initial.pres ++ spec._1).map(v => v.substitute(substitution).asInstanceOf[LogicTerm])
    val (shouldRestart, afterExhales) = extendedPres.reverse.foldLeft((false, afterArgNormalization))((acc, p) => {
      val (r, kb) = acc
      val strats = getRefoldingStrategiesAtInjectionPoint(inj)
      val (restart, result) = processExhaleLine(kb, ExhaleLine(ln, inj, p))
      val after = getRefoldingStrategiesAtInjectionPoint(inj)
      clearInjection(inj)
      addRefoldingStrategiesToInjectionPoint(inj, strats ++ after)
      (r || restart, result)
    })
    if (shouldRestart) {
      (true, afterExhales)
    }
    else {
      // reinitialize the targets
      val afterClearing = targets.foldLeft(afterExhales)((kb, t) => {
        val ref = kb.assignment.rc.freshValRef()
        kb.withAssignment(kb.assignment.assign(t.name, ref, t.typ))
      })

      // inhale the posts in correct order
      val extendedPosts = initial.posts ++ spec._2

      // replace the variables in the post conditions with the targets of the callsite
      val ts = MapTermSub(initial.res
        .map(a => VarTerm(a._1, a._2))
        .zip(targets)
        .toMap)
      val adjustedPosts = extendedPosts.map(e => e.substitute(substitution).substitute(ts).asInstanceOf[LogicTerm])

      // TODO: fix restart flag stuff
      val afterInhales = adjustedPosts.foldLeft(afterClearing)((kb, p) => processInhaleLine(kb, before, InhaleLine(ln, p))._2)

      println("<".repeat(100))
      println(method)
      println("<".repeat(100))
      println(ts)
      adjustedPosts.foreach(a => println(a.pretty()))
      println("<".repeat(100))

      println(afterInhales.pretty())

      println(">".repeat(100))
      println(">".repeat(100))

      (false, afterInhales)
    }
  }

  private def processExhaleLine(before: KnowledgeBase, line: ExhaleLine): (Boolean, KnowledgeBase) = {
    val ExhaleLine(ln, inj, exp) = line
    clearInjection(inj)

    // TODO: replace with processRequirements

    // TODO: check that all requirements are satisfied i.e. that all the field/pred permissions are provided
    //       -> generate and apply refolding strategies
    val (afterNorm, normTerm) = TermNormalization.normalizeMutablePartsInLogicTerm(before, before, exp)
    val folded = PredicateCollector.collectFoldedPredicates(this.engine, normTerm, afterNorm)
    val direct = PredicateCollector.collectDirectPredicates(this.engine, normTerm, afterNorm)
    val stripped = PredicateCollector.stripToPure(this.engine, normTerm, afterNorm)
    val partial = PredicateCollector.collectPotSatImpls(this.engine, normTerm, afterNorm)
    val baguettes = PredicateCollector.collectBaguettes(this.engine, normTerm, afterNorm)

    // TODO: this does not deal with missing magic wands and if they need to be  


    val afterUnfolding = direct.foldLeft(afterNorm)((kb, d) => {
      kb.findUnfoldingStrategy(this.engine, this.defs, d)
        .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
        .getOrElse(kb)
    })

    val afterRefolding = folded.foldLeft(afterUnfolding)((kb, f) => {
      kb.findRefoldingStrategy(this.engine, this.defs, f)
        .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
        .getOrElse(kb)
    })

    val afterPartial = partial.foldLeft(afterRefolding)((kb, p) => {
      kb.findUnfoldingStrategy(this.engine, this.defs, p)
        .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
        .getOrElse(kb)
    })

    val afterPartialRemoval = afterPartial.withPartial(afterPartial.partial.exhale(partial))

    val afterBaguette = baguettes.foldLeft(afterPartialRemoval)((kb, p) => {
      val strat = kb.findRepackagingStrategy(this.engine, this.defs, p)
      println(s"REPACK STRAT: ${p.pretty()} --> ${strat}")
        strat .map(s => {
          println(s"REPACKAGING STRATEGY FOR: ${p.pretty()}")
          println(s.pretty())
          applyRefoldingStrategy(this.engine, inj, kb, s)
        })
        .getOrElse(kb)
    })

    println("(".repeat(100))
    println("(".repeat(100))

    println(afterBaguette.pretty())

    println(")".repeat(100))
    println(")".repeat(100))

    val afterBaguetteRemoval = afterBaguette.withMWM(baguettes.foldLeft(afterBaguette.mwm)((a, b) => a.removeWand(b)))

    // TODO: detect that the predicate permissions are not fulfilled

    val resKb = afterBaguetteRemoval.update(a => h => d => f => fac => {
      val ud = direct.foldLeft(d)((a, b) => a.exhale(b))
      val uf = folded.foldLeft(f)((a, b) => a.exhale(b))
      val ufac = fac.and(stripped)
      (a, h, ud, uf, ufac)
    })

    val havoced = havocPassedFragment(resKb)

    (false, havoced)
  }

  private def processLocalAssignLine(before: KnowledgeBase, line: LocalAssignLine): (Boolean, KnowledgeBase) = {
    val LocalAssignLine(ln, inj, variable, value) = line
    clearInjection(inj)

    // collect and normalize the required fields
    val rawReqsValue = collectRequiredFieldPermissions(value)
    val (resNormKb, reqsValue) = TermNormalization.normalizeDirectRequirements(before, rawReqsValue.toSeq)

    // process the requirements and restart if modifications have been made
    val (restarting, kb) = processRequirements(ln, inj, resNormKb, reqsValue.toSet, Set())
    if (restarting) {
      (true, kb)
    }
    else {
      val (a2, refBeforeAssign) = kb.assignment.lookup(variable.name, variable.typ)
      val normKb = kb.withAssignment(a2)
      val (kbN, refN, _, infoN) = TermNormalization.computeNormalizedValueRef(normKb, normKb.assignment.rc, value)
      val ua = kbN.assignment.assign(variable.name, refN, variable.typ)

      val ts = MapTermSub(Map((variable, refBeforeAssign.toVarTerm(variable.typ))))
      val subbedInfo = kb.info.substitute(ts).asInstanceOf[LogicTerm] //.and(EqCmpTerm(variable, ))
      val resKb = KnowledgeBase(
        kbN.path,
        ua,
        kbN.heap,
        kbN.direct.substitute(ts),
        kbN.folded.substitute(ts),
        subbedInfo.and(infoN),
        kbN.partial.substitute(ts),
        kbN.mwm.substitute(ts),
        kbN.fieldTypes
      )
      (false, resKb)
    }
  }

  private def processFieldAssignLine(before: KnowledgeBase, line: FieldAssignLine): (Boolean, KnowledgeBase) = {
    val FieldAssignLine(ln, inj, fa, value) = line
    clearInjection(inj)

    val reqs = collectRequiredFieldPermissions(fa.src)
    val self = Set(PredFieldAccTerm(fa, PermFracTerm(IntTerm(1), IntTerm(1))))

    // TODO: this can be improved by first searching for all strategies and then deciding which strategies should be executed
    //       -> iteratively improve current standing until final state reached
    val combinedRaw = reqs.union(self)
    val reqsValueRaw = collectRequiredFieldPermissions(value)

    val (kbNormTarget, combined) = TermNormalization.normalizeDirectRequirements(before, combinedRaw.toSeq)
    val (kbNormValue, reqsValue) = TermNormalization.normalizeDirectRequirements(kbNormTarget, reqsValueRaw.toSeq)

    val (restarting, kb) = processRequirements(ln, inj, kbNormValue, (reqsValue ++ combined).toSet, Set())

    if (restarting) {
      (true, kb)
    }
    else {
      val (kbN, valueRef, typN, infoN) = TermNormalization.computeNormalizedValueRef(kb, kb.assignment.rc, value)
      val (kbS, objRef, typS, infoS) = TermNormalization.computeNormalizedValueRef(kbN, kbN.assignment.rc, fa.src)

      val (h4, fieldRef) = kbN.heap.lookupField(objRef, fa.field)
      val h5 = h4.assignField(objRef, fa.field, valueRef)
      // substitute the occurrences of this field usage with a temporary variable that refers to the val ref
      val ts = MapTermSub(Map((fa, VarTerm(s"t$$${fieldRef.id}", fa.typ))))
      val resKb = KnowledgeBase(
        kbS.path,
        kbS.assignment,
        h5,
        kb.direct.substitute(ts),
        kb.folded.substitute(ts),
        kb.info.substitute(ts).asInstanceOf[LogicTerm].and(infoN).and(infoS),
        kb.partial.substitute(ts),
        kbN.mwm.substitute(ts),
        kb.fieldTypes
      )

      (false, resKb)
    }
  }

  private def processInhaleLine(before: KnowledgeBase, line: InhaleLine): (Boolean, KnowledgeBase) = {
    processInhaleLine(before, before, line)
  }

  private def processInhaleLine(before: KnowledgeBase, old: KnowledgeBase, line: InhaleLine): (Boolean, KnowledgeBase) = {
    val InhaleLine(ln, exp) = line
    val rawFolded = PredicateCollector.collectFoldedPredicates(this.engine, exp, before)
    val rawDirect = PredicateCollector.collectDirectPredicates(this.engine, exp, before)
    val rawStripped = PredicateCollector.stripToPure(this.engine, exp, before)
    val rawPartial = PredicateCollector.collectPotSatImpls(this.engine, exp, before)
    val rawMagic = PredicateCollector.collectBaguettes(this.engine, exp, before)

    val (kb1, folded) = TermNormalization.normalizeFoldedRequirements(before, old, rawFolded)
    val (kb2, direct) = TermNormalization.normalizeDirectRequirements(kb1, old, rawDirect)
    val (kb3, stripped) = TermNormalization.normalizeLogicTerm(kb2, old, rawStripped)
    val (kb33, partial) = TermNormalization.normalizePotentialRequirements(kb3, old, rawPartial)
    val (kb4, baguettes) = TermNormalization.normalizeBaguetteRequirements(kb33, old, rawMagic)


    // TODO: normalize the folded, direct, partial and stripped (EVERYWHERE)
    val resKb = kb4.update((a, h, d, f, fac, pot, mag) => {
      val ud = direct.foldLeft(d)((a, b) => a.inhale(b))
      val uf = folded.foldLeft(f)((a, b) => a.inhale(b))
      val ufac = fac.and(stripped)
      val up = pot.inhale(partial)
      val um = baguettes.foldLeft(mag)((a, b) => a.addWand(b))
      (a, h, ud, uf, ufac, up, um)
    })

    val cleanedKb = resKb.cleanPotentialWithCurrentKnowledge(this.engine)

    (false, cleanedKb)
  }

  private def processNewObjLine(before: KnowledgeBase, line: NewObjLine): (Boolean, KnowledgeBase) = {
    val NewObjLine(ln, target, fields) = line
    // perform the assignment
    val (a2, refBeforeAssign) = before.assignment.lookup(target.name, target.typ)
    val valRef = a2.rc.freshValRef()
    val normTarget = valRef.toVarTerm(target.typ)
    val ua = a2.assign(target.name, valRef, target.typ)

    val afterAssign = KnowledgeBase(
      before.path, ua, before.heap, before.direct, before.folded, before.info, before.partial, before.mwm, before.fieldTypes
    )

    // substitute the old variable and inhale the new permissions
    val ts = MapTermSub(Map((target, VarTerm(s"t$$${refBeforeAssign.id}", target.typ))))
    val resKb = afterAssign.update(
      a => h => d => f => i => {
        val dir = fields.foldLeft(d.substitute(ts))((m, f) => {
          val fa = FieldAccTerm(normTarget, f._1, f._2)
          m.inhale(PredFieldAccTerm(fa, PermAmount.WRITE))
        })
        val fol = f.substitute(ts)
        val info = i.substitute(ts).asInstanceOf[LogicTerm].and(NotEqCmpTerm(target, NullTerm()))
        (a, h, dir, fol, info)
      }
    )

    (false, resKb)
  }

  def processLine(before: KnowledgeBase, line: Line): (Boolean, KnowledgeBase) = {
    line match {
      case bl: BranchLine => processBranchLine(before, bl)
      case ml: MergeLine => processMergeLine(before, ml)
      case al: AssertLine => processAssertLine(before, al)
      case al: AssumeLine => processAssumeLine(before, al)
      case cl: CallLine => processCallLine(before, cl)
      case ex: ExhaleLine => processExhaleLine(before, ex)
      case la: LocalAssignLine => processLocalAssignLine(before, la)
      case fa: FieldAssignLine => processFieldAssignLine(before, fa)
      case il: InhaleLine => processInhaleLine(before, il)
      case no: NewObjLine => processNewObjLine(before, no)
      case l => {
        throw new IllegalArgumentException(s"Unable to process line type ${l.getClass.getCanonicalName}")
      }
    }
  }

  private def findRequiredKnowledge(kb: KnowledgeBase, impl: ImplTerm, target: PredFieldAccTerm, depth: Int): Option[Set[LogicTerm]] = {
    // TODO: the knowledge base could be expanded with the contained information
    val direct: Seq[Option[Set[LogicTerm]]] = PredicateCollector.collectDirectPredicates(this.engine, impl.cons, kb)
      .filter(p => p.exp.equals(target.exp))
      .map(a => Some(Set[LogicTerm]()))
    val combined = if (depth > 0) {
      val folded = PredicateCollector.collectFoldedPredicates(this.engine, impl.cons, kb)
        .map(p => {
          val predDef = this.defs(p.pred.name)
          val body = predDef.instantiate(p.pred)
          val impl = ImplTerm(BoolTerm(true), body)
          findRequiredKnowledge(kb, impl, target, depth - 1)
        })

      val pot = PredicateCollector.collectPotSatImpls(this.engine, impl.cons, kb)
        .map(p => findRequiredKnowledge(kb, p, target, depth - 1))

      folded ++ pot
    }
    else Seq()
    val extended = (direct ++ combined)
      .flatten
      .map(v => v.union(Set(impl.prem)))

    if (extended.nonEmpty) {
      Some(extended.foldLeft(Set[LogicTerm]())((a, b) => a.union(b)))
    }
    else {
      None
    }
  }

  private def propagatePureConstraintThrough[P](ident: Ident, until: Ident, lp: LinePropagator[P], payload: P): AdjustmentResponse[P] = {
    if (ident.equals(this.currentMethod.start)) {
      val currentSpec = this.methSpec.getOrElse(this.currentMethod.method, (Seq(), Seq()))
      val currentPres = currentSpec._1
      val currentPosts = currentSpec._2
      this.methSpec.put(this.currentMethod.method, (currentPres ++ Seq(lp.toLT(payload)), currentPosts))
      println(s"PROPAGATED TO THE METHOD SPEC OF METHOD ${this.currentMethod.method}")
      SuccessfulAdjustment[P]()
    }
    else if (ident.equals(until)) {
      ContinueAdjustment(payload)
    }
    else {
      // TODO: what to do if different branches at a specific identifier cause different results?
      //       would this even be possible/problematic?
      // TODO: fix this
      val base = this.knowledge(ident).values.head
      println(s"THE PAYLOAD IS: ${payload}")
      // TODO: the payload might not be verifiable like: !acc(SOME, VALUE)
      val proofRes = this.engine.prove(base, lp.toLT(payload))
      if (proofRes == Sat) {
        // knowledge is already fulfilled at the current branch and should thus not be propagated further
        SuccessfulAdjustment[P]()
      }
      else if (proofRes == UnSat) {
        // the constraint is unsatisfiable within this context -> idk how to deal with that but for know keep propagating
        FailedAdjustment[P]()
      }
      else {
        val line = this.currentMethod.rep.getLine(ident)
        lp.apply(line, payload)
      }
    }
  }

  private def getNullPropagator(): LinePropagator[Term] = {
    LinePropagator((l, p) => l match {
      //        case AssertLine(ln, inj, exp) =>
      //        case AssumeLine(ln, exp) =>
      //        case BranchLine(ln, pre, cond, thn, els) =>
      //        case CallLine(ln, inj, method, targets, args) =>
      //        case ExhaleLine(ln, inj, exp) =>
      //        case FieldAssignLine(ln, inj, fa, value) =>
      //        case InhaleLine(ln, exp) =>
      //        case LocalAssignLine(ln, inj, variable, value) =>
      //        case MergeLine(ln, correspondingBranch, postThnInj, postElsInj, lastThn, lastEls) =>
      case NewObjLine(ln, target, fields) => {
        // check if target == term -> this is a contradiction since a fresh object can not be null
        if (p.equals(target)) {
          FailedAdjustment[Term]()
        }
        else if (isJustFieldsOnVariable(p)) {
          p match {
            case FieldAccTerm(base: VarTerm, field, _) => if (target.equals(base)) {
              SuccessfulAdjustment[Term]()
            }
            else {
              ContinueAdjustment[Term](p)
            }
            case _ => ContinueAdjustment[Term](p)
          }
        }
        else {
          // otherwise reverse map the assignment of the variable and replace the temporary variables within the current term
          // TODO: fix this
          ContinueAdjustment[Term](p)
        }

        FailedAdjustment[Term]()
      }
      case c => {
        throw new IllegalArgumentException(s"Unable to process line of type ${l.getClass.getCanonicalName} while propagating null constraint!")
      }
    },
      t => EqCmpTerm(t, NullTerm()))
  }

  private def isJustFieldsOnVariable(term: Term): Boolean = {
    term match {
      case AddTerm(a, b) => false
      case FieldAccTerm(src, field, typ) => isJustFieldsOnVariable(term)
      case IntTerm(value) => false
      case term: LogicTerm => false
      case VarTerm(name, typ) => true
      case MulTerm(a, b) => false
      case NegTerm(t) => false
      case NullTerm() => false
      case PermFracTerm(a, b) => false
      case SubTerm(a, b) => false
      case _ => false
    }
  }

  private def collectFieldsAndBaseVariable(term: Term): (VarTerm, Seq[String]) = {
    term match {
      case FieldAccTerm(src, field, typ) => {
        val sub = collectFieldsAndBaseVariable(src)
        (sub._1, sub._2 ++ Seq(field))
      }
      case v: VarTerm => (v, Seq())
      case _ => {
        throw new IllegalArgumentException(s"Unable to collect base variable and fields of term: ${term.pretty()}")
      }
    }
  }

  private def getNonNullPropagator(): LinePropagator[Term] = {
    LinePropagator((l, t) => {
      l match {
        //        case AssertLine(ln, inj, exp) =>
        //        case AssumeLine(ln, exp) =>
        //        case BranchLine(ln, pre, cond, thn, els) =>
        //        case CallLine(ln, inj, method, targets, args) =>
        //        case ExhaleLine(ln, inj, exp) =>
        //        case FieldAssignLine(ln, inj, fa, value) =>
        //        case InhaleLine(ln, exp) =>
        //        case LocalAssignLine(ln, inj, variable, value) =>
        //        case MergeLine(ln, correspondingBranch, postThnInj, postElsInj, lastThn, lastEls) =>
        case NewObjLine(ln, target, fields) => {
          // check if target == term -> perfect since a fresh object is never null
          if (t.equals(target)) {
            SuccessfulAdjustment()
          }
          else if (isJustFieldsOnVariable(t)) {
            val (base, fields) = collectFieldsAndBaseVariable(t)
            if (base.equals(target)) {
              // problem since the fields are all null
              FailedAdjustment()
            }
            else {
              // otherwise reverse map the assignment of the variable and replace the temporary variables within the current term
              // TODO: fix the substitution of the term
              val subbed = t
              ContinueAdjustment(subbed)
            }
          }
          else {
            // TODO: fix this. Is it even possible that this case is reached?
            FailedAdjustment()
          }
        }
        case l => {
          throw new IllegalArgumentException(s"Unable to prop non null through line ${l.getClass.getCanonicalName}")
        }
      }
    },
      t => NotEqCmpTerm(t, NullTerm()))

  }

  private def getLinePropagator(pure: Comparison): (LinePropagator[Term], Term) = {
    pure match {
      case EqCmpTerm(a, NullTerm()) => (getNullPropagator(), a)
      case EqCmpTerm(NullTerm(), a) => (getNullPropagator(), a)
      case NotEqCmpTerm(a, NullTerm()) => (getNonNullPropagator(), a)
      case NotEqCmpTerm(NullTerm(), a) => (getNonNullPropagator(), a)
        //      case GreaterCmpTerm(a, b) =>
        //      case GreaterEqCmpTerm(a, b) =>
        //      case LessCmpTerm(a, b) =>
        //      case LessEqCmpTerm(a, b) =>
        //      case NotEqCmpTerm(a, b) =>
        //      case EqCmpTerm(a, b) =>
      case c => {
        throw new IllegalArgumentException(s"Unable to construct propagator for constraint: ${pure.pretty()}")
      }
    }
  }

  private def propagatePureConstraints(ident: Ident, pure: LogicTerm, kb: KnowledgeBase): Boolean = {
    val preds = this.currentMethod.rep.getPredecessors(ident)

    val simplified = LogicTermRewriting.simplify(pure)
    val bmI = kb.constructInfoBackMapping()
    val bmH = kb.constructBackMapping(this.currentMethod, useAllVariables = true)
    val bm = bmH.followedBy(bmI)
    val backmapped = simplified.substitute(bm)
    println(s"ADDITIONAL REQUIREMENTS THAT NEED TO BE PROPAGATED!:")
    println(simplified.pretty())
    println(backmapped.pretty())

    val responses = backmapped match {
      case c: Comparison => {
        val (lp, pay) = getLinePropagator(c)

        preds.map(i => {
          propagatePureConstraintThrough(i, this.currentMethod.start, lp, pay)
        })
      }
      case _ => Seq()
    }


    responses.exists {
      case SuccessfulAdjustment() => true
      case ContinueAdjustment(_) => false
      case FailedAdjustment() => false
      case _ => false
    }
  }

  private def findIfPotHasSolution(current: Ident, kb: KnowledgeBase, target: PredFieldAccTerm, amount: Term): Boolean = {
    val implSearchDepth = 10
    println(s"CHECKING IN IMPLICATIONS FOR: ${target.pretty()}")
    val reqs = kb.partial.partial.toSeq
      .flatMap(a => findRequiredKnowledge(kb, a, target, implSearchDepth))
      .foldLeft(Set[LogicTerm]())((a, b) => a.union(b))

    println(s"REQS:")
    reqs.foreach(a => println(a.pretty()))

    if (reqs.nonEmpty) {
      // TODO: joining like this would prevent something like: (A ==> REQ)  &  (!A ==> REQ)
      val pure = reqs.map(r => PredicateCollector.stripToPure(this.engine, r, kb))
        .reduceLeftOption((a, b) => a.and(b))
        .getOrElse(BoolTerm(true))
      propagatePureConstraints(current, pure, kb)
    }
    else {
      false
    }
  }

  private def setKnowledgeBase(ident: Ident, kb: KnowledgeBase): Unit = {
    val before = this.knowledge.getOrElse(ident, Map())
    val after = before.updated(kb.path.map(_._2), kb)
    this.knowledge.put(ident, after)
  }

  private def testMW(fieldTypes: Map[String, Type]): Unit = {
    val count = RefCounter(Counter(0))

    val x = VarTerm("x", Ref)
    val kb = KnowledgeBase(
      Seq(),
      new Assignment(count),
      new Heap(count),
      new DirectPermissionMask(Map(
        (FieldAccTerm(x, "aaa", Int), PermAmount.READ),
        (FieldAccTerm(x, "bbb", Int), PermAmount.READ)
      )),
      new FoldedPermissionMask(),
      BoolTerm(true),
      new Potential(),
      new MagicWandManager(),
      fieldTypes
    )

    val wand = BaguetteMagic(
      Set(PredFieldAccTerm(FieldAccTerm(x, "aaa", Int), PermAmount.READ)),
      Set(),
      Set(),
      Set(),
      Set(PredInstAccTerm(PredInst("Comb", Seq(x)), PermAmount.READ)),
      Set()
    )
    val steps = Seq(
      FoldingStep(PredInst("Comb", Seq(x)), PermAmount.READ)
    )

    val strats = Seq(RefoldingStrategy(Seq(
      PackageStep(wand, steps),
      ApplyStep(wand, PermAmount.WRITE)
    )))

    applyStrategies(this.engine, null, kb, strats)

    if (true) {
      throw new IllegalArgumentException("STOPPING")
    }
  }

  def infer(program: Program, meth: InternalMethod, inductionStart: Boolean) = {
    // generate mapping of field definitions to their corresponding type
    val fieldTypes = program.fields.map(f => f.name -> f.typ).toMap

    this.knowledge.clear()
    val counter = RefCounter(Counter(0))

    val mesh = meth.rep.mesh
    val lines = meth.rep.lines

    //    testMW(fieldTypes)

    var restarting = true
    while (restarting) {
      this.knowledge.clear()
      restarting = false

      // generate an initial assignment based of the arguments of the method
      val initAssignment = meth.args.foldLeft(new Assignment(counter))((a, f) => a.assign(f._1, counter.freshValRef(), f._2))
      val empty = KnowledgeBase(Seq(), initAssignment, new Heap(counter), new DirectPermissionMask(), new FoldedPermissionMask(), BoolTerm(true), new Potential(), new MagicWandManager(), fieldTypes)

      // inhale the preconditions
      // TODO: fix the restart position
      val mergedPres = meth.pres ++ this.methSpec(this.currentMethod.method)._1
      val afterPres = mergedPres.foldLeft(empty)((kb, p) => processLine(kb, InhaleLine(meth.start, p))._2)
      setKnowledgeBase(meth.start, afterPres)

      var open = mesh(meth.start).toSeq

      while (!restarting && open.nonEmpty) {
        val current = open.head
        println(s"processing line: ${current}")

        val kbs = mesh.filter(e => e._2.contains(current))
          .keys
          .flatMap(i => {
            val entries = if(this.knowledge.contains(i))
              this.knowledge(i).values
            else Seq()
            if (lines.contains(i)) {
              lines(i) match {
                case BranchLine(ln, pre, cond, thn, els) => {
                  val assumption = if (thn == current) cond else NotTerm(cond)
                  val ident = if(thn == current) thn else els
                  entries
                    .map(k => {
                      val (norm, t) = TermNormalization.normalizeMutablePartsInLogicTerm(k, k, assumption)
                      norm.withPath(ident, assumption).extendInfo(t)
                    })
                }
                case _ => entries
              }
            } else {
              entries
            }
          })

        kbs.foreach(k => println(k.pretty()))

        kbs.foreach(kb => {
          if (!restarting) {
            val line = lines(current)
            println(s"line: ${line.pretty()}")

            val (shouldRestart, after) = processLine(kb, line)
            restarting = shouldRestart

            println(s"SHOULD RESTART: ${restarting}")


            println(s":::::::::::::::: AFTER ${current.pretty()} :::::::::::::::::")
            println(after.pretty())

            setKnowledgeBase(current, after)
          }
        })

        open = open.tail ++ mesh(current).toSeq
      }
    }
    if (!restarting) {

      val startKbs = this.knowledge(meth.start).values
      if (startKbs.size != 1) {
        throw new IllegalArgumentException("Expected a single knowledge base at the start of the method!")
      }

      val startKb = startKbs.head
      val finalKbs = this.knowledge(meth.stop).values
      val mergedPosts = (meth.posts ++ this.methSpec(this.currentMethod.method)._2).reverse

      println("ALL POSTS FOR METHOD:")
      mergedPosts.foreach(a => println(s"-----> ${a.pretty()}"))

      val afterPostsKbs = finalKbs.map(finalKb => {

        val finInj = this.currentMethod.finalInj

        on(this.engine, startKb, finalKb, meth)

        val lastInjection = findEarliestInjectionPoint(finalKb)

        val afterPosts = mergedPosts.foldLeft(finalKb)((kb, p) => {
          // saving the current injections since they get reset by processing the exhale line
          val beforeReset = this.injections.getOrElse(lastInjection, Seq())
          println(s"PROCESSING: ${p.pretty()}  -> ${kb.path.map(_._2).map(_.pretty())}")
          val result = processExhaleLine(kb, ExhaleLine(meth.stop, lastInjection, p))._2
          // restoring the old injections in addition to the current injections
          val afterReset = this.injections.getOrElse(lastInjection, Seq())
          this.injections.put(lastInjection, beforeReset ++ afterReset)
          result
        })

        afterPosts
      })

      if(inductionStart) {
        val nullGuardedReconstruction = (kb: KnowledgeBase, v: VarTerm, pred: PredInstAccTerm) => {
          // check if v != null ==> pred(v) can be reconstructed

          // backmapping for eliminating temporary variables in the post conditions
          val bmH = kb.constructBackMapping(this.currentMethod, useAllVariables = true)
          val bmI = kb.constructInfoBackMapping()
          val bm = bmH.followedBy(bmI)

          val premise = NotEqCmpTerm(v, NullTerm())
          val impl = ImplTerm(premise, pred)
          val implicationAvailable = kb.partial.partial.contains(impl)
          if (implicationAvailable) {
            println(s"ITS AVAILABLE IN THE IMPLICATIONS ${impl.pretty()}")
            // implication is available in the partial information
            // no need to do anything
            Some((kb, RefoldingStrategy(Seq()), Some(impl.rewrite(bm))))
          }
          else {
            val variableMustBeNonNull = this.engine.provePure(kb, premise) == Sat
            if (variableMustBeNonNull) {
              println(s"SEARCHING REFOLDING STRATEGY ${impl.pretty()}")
              kb.findRefoldingStrategy(this.engine, this.defs, pred)
                .map(s => {
                  println(s"FOUND STRATEGY ${impl.pretty()}")
                  println(s.pretty())
                  (kb, s, Some(impl.rewrite(bm)))
                })
            }
            else {
              println(s"ITS VARIABLE IS NULL ${impl.pretty()}")
              Some((kb, RefoldingStrategy(Seq()), Some(impl.rewrite(bm))))
            }
          }
        }

        val nullGuardedMagicWandReconstruction = (kb: KnowledgeBase, v: VarTerm, pred: PredInstAccTerm) => {
          // backmapping for eliminating temporary variables in the post conditions
          val bmH = kb.constructBackMapping(this.currentMethod, useAllVariables = true)
          val bmI = kb.constructInfoBackMapping()
          val bm = bmH.followedBy(bmI)

          val premise = NotEqCmpTerm(v, NullTerm())
          val variableMustBeNonNull = this.engine.provePure(kb, premise) == Sat
          if (variableMustBeNonNull) {
            attemptMagicWandConstruction(kb, v, pred)
              .map(s => (kb, s._2, Some(s._1.rewrite(bm))))
          }
          else {
            Some((kb, RefoldingStrategy(Seq()), None))
          }
        }

        val reconstructionMethods: Seq[(KnowledgeBase, VarTerm, PredInstAccTerm) => Option[(KnowledgeBase, RefoldingStrategy, Option[LogicTerm])]] = Seq(
          nullGuardedReconstruction,
          nullGuardedMagicWandReconstruction
        )

        val originalTypes = program.inferInfo.typeAnnotations(this.currentMethod.method)._1
        val argumentNames = this.currentMethod.args.map(a => a._1)
        val (resultingKbs, proposableWands) = argumentNames.zip(originalTypes)
          .filter(a => a._2.isInstanceOf[DatatypeType])
          .foldLeft((afterPostsKbs, Seq[(String, BaguetteMagic)]()))((acc, arg) => {

            val paramType = arg._2.asInstanceOf[DatatypeType]
            // TODO: fix the name mangling to actually cover the generic name mangling stuff
            val predName = paramType.datatypeName

            val successfullyReconstructed = reconstructionMethods.foldLeft((false, acc._1))((state, rec) => {
              val successfulReconstruction = true
              val failedReconstruction = false

              val (alreadySuccessful, kbs) = state

              if (!alreadySuccessful) {
                val specTerms = kbs.map(kb => {
                  val originalRef = kb.assignment.variables(arg._1)._1.toVarTerm(Ref)
                  val orgPred = PredInstAccTerm(PredInst(predName, Seq(originalRef)), PermAmount.WRITE)

                  rec(kb, originalRef, orgPred)
                })

                // merge all options into a single option
                val merged = specTerms.foldLeft[Option[Seq[(KnowledgeBase, RefoldingStrategy, Option[LogicTerm])]]](Some(Seq()))((a, b) => (a, b) match {
                  case (Some(l), Some(v)) => Some(l ++ Seq(v))
                  case _ => None
                })

                merged match {
                  case Some(value) => {
                    // adjust the method specification (assumes at least one path exists)
                    val terms = value.flatMap(t => t._3)
                    println(s"BAGUETTE TERMS: ${terms.map(_.pretty())}")
                    if (terms.nonEmpty && terms.forall(t => t.equals(terms.head))) {
                      val (pres, posts) = this.methSpec(this.currentMethod.method)
                      this.methSpec.put(this.currentMethod.method, (pres, posts ++ Seq(terms.head)))

                      // apply the refolding strategies
                      val adjusted = value.map(t => {
                        val (kb, strat, _) = t
                        val injection = findEarliestInjectionPoint(kb)
                        applyStrategies(this.engine, injection, kb, Seq(strat))
                      })

                      (successfulReconstruction, adjusted)
                    }
                    else {
                      (failedReconstruction, kbs)
                    }
                  }
                  case None => (failedReconstruction, kbs)
                }
              }
              else {
                (failedReconstruction, kbs)
              }
            })

            if (successfullyReconstructed._1) {
              (successfullyReconstructed._2, acc._2)
            }
            else {
              val mappedReconstructions = acc._1.filter(isBaseCasePath)
                .map(a => {
                  println(a.path.map(_._2).map(_.pretty()))
                  a
                })
                .map(kb => {
                  val originalRef = kb.assignment.variables(arg._1)._1.toVarTerm(Ref)
                  val orgPred = PredInstAccTerm(PredInst(predName, Seq(originalRef)), PermAmount.WRITE)
                  val result = nullGuardedMagicWandReconstruction(kb, originalRef, orgPred)
                  (kb.path, result)
                })

              println(s"MAPPED RECONSTRUCTION BASE CASES: ${mappedReconstructions.size}")

              val allSuccessful = mappedReconstructions.forall(a => a._2.isDefined)
              val wands = mappedReconstructions.flatMap(v => v._2).flatMap(v => v._3)

              if (allSuccessful && wands.nonEmpty) {
                val allSameWands = wands.forall(w => w.equals(wands.head))
                if (allSameWands) {

                  println("reconstructed wands:")
                  wands.foreach(a => println(a.pretty()))

                  println("MAPPED RECONSTRUCTIONS:")
                  mappedReconstructions.foreach(a => {
                    println(a._1.map(a => a._2.pretty()).mkString(" -> "))
                    println(a._2.flatMap(_._3.map(a => a.pretty())))
                  })
                  (acc._1, acc._2 ++ Seq((arg._1, wands.head)))
                }
                else {
                  acc
                }
              }
              else {
                // no proposable magic wand found
                acc
              }
            }
          })

        println("PROPOSABLE WANDS:")
        proposableWands.foreach(w => {
          println(s"${w._1}: ${w._2.pretty()}")
        })

        proposableWands

        // TODO: add a final test which checks if the inferred method spec can be verified
      }
      else {
        Seq()
      }
    }
    else {
      Seq()
    }

    //      if (true) {
    //        //        dumpBeautifiedKbs()
    //
    //        dumpUntangledKbs()
    //        val (pres, posts) = this.methSpec(this.currentMethod.method)
    //        println("ADJUSTED METHOD SPEC:")
    //        println(pres.map(_.pretty()))
    //        println(posts.map(_.pretty()))
    //        //        dumpRawKbs()
    //      }

  }

  private def isBaseCasePath(kb: KnowledgeBase): Boolean = {
    println(s"lines on path: ${kb.path.map(a => a._1.pretty() + "  " + a._2.pretty()).mkString(" -> ")}")
    computeLinesOnPathFromEnd(kb).foreach(println)

    !computeLinesOnPathFromEnd(kb).exists {
      case CallLine(_, _, name, _, _) => name.equals(this.currentMethod.method)
      case _ => false
    }
  }

  private def computeLinesOnPathFromEnd(kb: KnowledgeBase): Seq[Line] = {
    computeLinesOnPathFromIdent(kb, this.currentMethod.stop)
  }

  private def computeLinesOnPathFromIdent(kb: KnowledgeBase, current: Ident): Seq[Line] = {
    if (current == this.currentMethod.start) {
      Seq()
    }
    else {
      val mesh = this.currentMethod.rep.mesh
      val lines = this.currentMethod.rep.lines
      val currentLine = lines(current)
      val sub = currentLine match {
        case MergeLine(ln, correspondingBranch, postThnInj, postElsInj, lastThn, lastEls) => {
          val correspBranch = lines(correspondingBranch).asInstanceOf[BranchLine]
          if (kb.path.exists(n => n._1.equals(correspBranch.thn))) {
            computeLinesOnPathFromIdent(kb, lastThn)
          }
          else {
            computeLinesOnPathFromIdent(kb, lastEls)
          }
        }
        case l => {
          computeLinesOnPathFromIdent(kb, mesh.filter(e => e._2.contains(l.ln))
            .head._1)
        }
      }
      sub ++ Seq(currentLine)
    }


  }

  private def applyBm(bm: TermSub, term: Term): Term = {
    FixedPoint.compute(term, (s: Term) => s.substitute(bm))
  }

  private def getSinglePredecessor(mesh: mutable.HashMap[Ident, mutable.HashSet[Ident]], ident: Ident): Ident = {
    mesh.toMap.filter(e => e._2.contains(ident)).keys.toSeq.head
  }

  private def findEarliestInjectionPoint(kb: KnowledgeBase): Injection = {
    val mesh = this.currentMethod.rep.mesh
    val lines = this.currentMethod.rep.lines
    var current = this.currentMethod.stop
    var bestInjection: Injection = this.currentMethod.finalInj
    var running = true
    while (current != this.currentMethod.start && running) {
      val line: Line = lines(current)
      current = line match {
        // improve localization by detecting if assignment conflicts with folding
        case LocalAssignLine(ln, inj, _, _) => {
          running = false
          getSinglePredecessor(mesh, ln)
        }
        case FieldAssignLine(ln, inj, _, _) => {
          running = false
          getSinglePredecessor(mesh, ln)
        }
        case AssumeLine(ln, _) => {
          getSinglePredecessor(mesh, ln)
        }
        case AssertLine(ln, inj, _) => {
          bestInjection = inj
          getSinglePredecessor(mesh, ln)
        }
        case InhaleLine(ln, _) => getSinglePredecessor(mesh, ln)
        case ExhaleLine(ln, inj, _) => {
          bestInjection = inj
          getSinglePredecessor(mesh, ln)
        }
        case BranchLine(ln, _, _, _, _) => {
          getSinglePredecessor(mesh, ln)
        }
        case MergeLine(_, correspondingBranch, postThnInj, postElsInj, lastThn, lastEls) => {
          val bline = lines(correspondingBranch).asInstanceOf[BranchLine]
          if (kb.path.exists(a => a._1.equals(bline.thn))) {
            // knowledge base from the then branch
            bestInjection = postThnInj
            lastThn
          }
          else {
            // knowledge base from the else branch
            bestInjection = postElsInj
            lastEls
          }
        }
        case CallLine(ln, inj, _, _, _) => {
          running = false
          getSinglePredecessor(mesh, ln)
        }
        case NewObjLine(ln, _, _) => getSinglePredecessor(mesh, ln)
      }
    }
    bestInjection
  }

  private def dumpUntangledKbs(): Unit = {
    println("::::::::::::::::::::::::::::::::: KB DUMP (UNTANGLED) :::::::::::::::::::::::::::::::::")
    this.knowledge.toSeq
      .sortBy(v => v._1.value)
      .foreach(e => {
        println(s"Identifier: ${e._1.pretty()}")
        e._2.foreach(k => {
          println(s"Path: ${k._1.map(_.pretty()).mkString("  &&  ")}".indent(2))
          //          println("----")
          //          println(k._2.pretty().indent(4))
          //          println("----")
          val kb = LogicTermRewriting.untangle(k._2)
          println(kb.pretty())
          val bmH = kb.constructBackMapping(this.currentMethod, useAllVariables = true)
          val bmI = kb.constructInfoBackMapping()
          val bm = bmH.followedBy(bmI)
          println("direct beautiful:")
          kb.direct.permissions.foreach(p => {
            println(s"  ${applyBm(bm, p._1).pretty()}: ${TermRewriter.simplify(applyBm(bm, p._2)).pretty()}")
          })
          println("folded beautiful:")
          kb.folded.permissions.foreach(p => {
            println(s"  ${PredInst(p._1.name, p._1.args.map(a => applyBm(bm, a))).pretty()}: ${TermRewriter.simplify(applyBm(bm, p._2)).pretty()}")
          })
          //          println("----------- untangled -------------")
          //          LogicTermRewriting.untangle(kb)
        })
      })
    println(":::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
  }


  private def dumpBeautifiedKbs(): Unit = {
    println("::::::::::::::::::::::::::::::::: KB DUMP (BEAUTIFIED) :::::::::::::::::::::::::::::::::")
    this.knowledge.toSeq
      .sortBy(v => v._1.value)
      .foreach(e => {
        println(s"Identifier: ${e._1.pretty()}")
        e._2.foreach(k => {
          println(s"Path: ${k._1.map(_.pretty()).mkString("  &&  ")}".indent(2))
          val kb = k._2
          println(kb.pretty())
          val bmH = kb.constructBackMapping(this.currentMethod, useAllVariables = true)
          val bmI = kb.constructInfoBackMapping()
          val bm = bmH.followedBy(bmI)
          println("direct beautiful:")
          kb.direct.permissions.foreach(p => {
            println(s"  ${applyBm(bm, p._1).pretty()}: ${TermRewriter.simplify(applyBm(bm, p._2)).pretty()}")
          })
          println("folded beautiful:")
          kb.folded.permissions.foreach(p => {
            println(s"  ${PredInst(p._1.name, p._1.args.map(a => applyBm(bm, a))).pretty()}: ${TermRewriter.simplify(applyBm(bm, p._2)).pretty()}")
          })
          //          println("----------- untangled -------------")
          //          LogicTermRewriting.untangle(kb)
        })
      })
    println(":::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
  }

  private def dumpRawKbs(): Unit = {
    println("::::::::::::::::::::::::::::::::: KB DUMP :::::::::::::::::::::::::::::::::")
    this.knowledge.toSeq
      .sortBy(v => v._1.value)
      .foreach(e => {
        println(s"Identifier: ${e._1.pretty()}")
        e._2.foreach(k => {
          println(s"Path: ${k._1.map(_.pretty()).mkString("  &&  ")}".indent(2))
          println(k._2.pretty().indent(4))
        })
      })
    println(":::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
  }

  // TODO: add dummy line that can be used by the merge line to similarize the knowledge bases as far as possible
  //       fold and unfold the different parts that are available to match each other so that a single permission story/refolding strategy is able to be applied to all the knowledge bases
  //       maybe think about using potential knowledge bases
  // TODO: split this file into smaller parts
  // TODO: maybe consider all knowledge bases at the same time. synthesize a single refolding strategy and check against all other knowledge bases

  private def on1(engine: ReasoningEngine, kb: KnowledgeBase, objRef: ValRef, ibm: TermSub, bm: TermSub): Unit = {
    if (kb.heap.objMap.contains(objRef)) {
      val obj = kb.heap.objMap(objRef)
      val source = objRef.toVarTerm(Ref)
      //      println(s"${objRef.pretty()}: ${source.substitute(bm).pretty()}  ==  old(${source.substitute(ibm).pretty()})")
      obj.fields.foreach(f => {
        // TODO: this can be adjusted to only check for > 0 permissions and not a specific amount
        val desired = PermAmount.READ
        val access = FieldAccTerm(source, f._1, kb.fieldTypes(f._1))
        val pred = PredFieldAccTerm(access, desired)
        if (engine.proveWithPotential(kb, pred) == Sat) {
          val value = f._2.toVarTerm(kb.fieldTypes(f._1))
          println(s"${access.substitute(ibm).pretty()}  := old(${value.substitute(ibm).pretty()})")
        }
      })
    }
  }

  private def on(engine: ReasoningEngine, start: KnowledgeBase, kb: KnowledgeBase, meth: InternalMethod): Unit = {
    val args = Some()
    // applying the back mapping like this assumes that the contents of the parameter arguments can not be altered
    val backmapping = kb.constructBackMapping(meth, useAllVariables = false)
    val initialBackmapping = kb.constructInitialBackMapping(meth, useAllVariables = false)
    //    println("CHECKING THE STATE AFTER:")
    //    println(s"IBM: ${initialBackmapping}")
    //    println(s"BM: ${backmapping}")
    kb.heap.objMap.foreach(e => {
      on1(engine, kb, e._1, initialBackmapping, backmapping)
    })
    //    println("CHECKING WHAT THE ARGS ARE ABOUT:")
    //    meth.args.foreach(a => {
    //      val value = kb.assignment.variables(a._1)
    //      val backmapped = value._1.toVarTerm(value._2).substitute(backmapping)
    //      println(s"${value._1.pretty()}   => ${backmapped.pretty()}")
    //      val obj = kb.heap.objMap(value._1)
    //      println("CHECKING THE FIELDS OF THE OBJECT:")
    //      obj.fields.foreach(f => {
    //        val res = f._2.toVarTerm(kb.fieldTypes(f._1)).substitute(backmapping)
    //        println(s"${f._1}: ${res.pretty()}")
    //      })
    //    })
    //    println(s"CHECKING THE INFO: ${kb.info.substitute(backmapping).pretty()}")
  }
}


case class Inference(verifier: Verifier, defs: Map[String, PredDef], reps: Map[String, InternalMethod], program: Program, methSpec: mutable.HashMap[String, (Seq[LogicTerm], Seq[LogicTerm])]) {

  def printSpec(spec: (Seq[LogicTerm], Seq[LogicTerm])): Unit = {
    println("pres:")
    spec._1.foreach(e => println(e.pretty().indent(2)))
    println("posts:")
    spec._2.foreach(e => println(e.pretty().indent(2)))
  }

  private def createPredAccPred(pred: PredInst, perm: Term): PredicateAccessPredicate = {
    PredicateAccessPredicate(
      PredicateAccess(pred.args.map(e => e.toExp()), pred.name)(),
      Some(perm.toExp())
    )()
  }

  private def convertRefoldingStep(step: RefoldingStep): Seq[Stmt] = {
    step match {
      case FoldingStep(pred, perm) => {
        Seq(Fold(createPredAccPred(pred, perm))())
      }
      case UnfoldingStep(pred, perm, subs) => {
        val self = Unfold(createPredAccPred(pred, perm))()
        val internal = subs.flatMap(s => convertRefoldingStep(s))
        Seq(self) ++ internal
      }
      case PackageStep(wand, steps) => {
        println(s"WAND: ${wand.pretty()}")
        val internal = steps.flatMap(s => convertRefoldingStep(s))
        val proof = Seqn(internal, Seq())()
        val premise = wand.premTerms().reduceLeft((a, b) => AndTerm(a, b)).toExp()
        val consequence = wand.consTerms().reduceLeft((a, b) => AndTerm(a, b)).toExp()
        val magic = MagicWand(premise, consequence)()
        val self = Package(magic, proof)()
        Seq(self)
      }
        // TODO: eliminate perm from the apply step
      case ApplyStep(wand, perm) => {

        val premise = wand.premTerms().reduceLeft((a, b) => AndTerm(a, b)).toExp()
        val consequence = wand.consTerms().reduceLeft((a, b) => AndTerm(a, b)).toExp()
        val magic = MagicWand(premise, consequence)()

        val self = Apply(magic)()
        Seq(self)
      }
      case _ => {
        throw new IllegalArgumentException(s"Unable to convert refolding step of type ${step.getClass.getCanonicalName}")
      }
    }
  }

  private def convertRefoldingStrategy(injections: Seq[RefoldingStrategy]): Stmt = {
    val stmts = injections.flatMap(strat => strat.steps.flatMap(convertRefoldingStep))
    Seqn(stmts, Seq())()
  }

  private def injectRefoldingStrategySeqn(strats: Map[Injection, Seq[RefoldingStrategy]], s: Seqn): Seqn = {
    val injected = s.ss.map(s => injectRefoldingStrategy(strats, s))
    Seqn(injected, s.scopedSeqnDeclarations)(s.pos, s.info, s.errT)
  }

  private def injectRefoldingStrategy(strats: Map[Injection, Seq[RefoldingStrategy]], stmt: Stmt): Stmt = {
    stmt match {
      case i: Injection => convertRefoldingStrategy(strats.getOrElse(i, Seq()))
      case s: Seqn => injectRefoldingStrategySeqn(strats, s)
      case s@If(cond, thn, els) => {
        val mappedThn = injectRefoldingStrategy(strats, thn).asInstanceOf[Seqn]
        val mappedEls = injectRefoldingStrategy(strats, els).asInstanceOf[Seqn]
        If(cond, mappedThn, mappedEls)(s.pos, s.info, s.errT)
      }
        // TODO: extend for while stmt
        //      case e => {
        //        throw new IllegalArgumentException(s"Unable to inject folding story into ${e.getClass.getName}")
        //      }
      case s => s
    }
  }

  private def generateDtTypeRequirement(name: String, dt: DatatypeType, lowered: Type): LogicTerm = {
    val input = VarTerm(name, lowered)
    ImplTerm(
      NotEqCmpTerm(input, NullTerm()),
      PredInstAccTerm(PredInst(dt.datatypeName, Seq(input)), PermAmount.WRITE)
    )
  }


  def infer(): Unit = {
    // initialize empty additional specs for all methods
    this.reps.keySet.foreach(k => {
      val dtBasedPres = this.program.inferInfo.typeAnnotations(k)._1.zip(this.reps(k).args)
        .flatMap(v => v._1 match {
          case d: DatatypeType => Some(generateDtTypeRequirement(v._2._1, d, v._2._2))
          case _ => None
        })

      val dtBasedPosts = this.program.inferInfo.typeAnnotations(k)._2.zip(this.reps(k).res)
        .flatMap(v => v._1 match {
          case d: DatatypeType => Some(generateDtTypeRequirement(v._2._1, d, v._2._2))
          case _ => None
        })
      this.methSpec.put(k, (dtBasedPres, dtBasedPosts))
    })
    // TODO: maybe extend inference fields with outline information etc

    // TODO: example identity function
    //       if one use case requires: ret != null
    //       and another use case just needs: id != null ===> ret != null because it might supply null to the function
    //       the first case would cause the function to require id != null which causes problems for the second function
    //       the second use would need the function to accept null values => this causes a contradiction
    //       => a more precise characterization of the function without imposing stuff first would make it clear that
    //          ret != null is only fulfilled when id != null and this does not impose a specific restriction of the function itself
    //          the function should specify that either ret == id or id != null ==> ret != null
    //          so that its use case specific and can be adapted for each of the uses
    //   ======> maybe this can be avoided by processing the methods in a topological order?

    val order = DependencyAnalysis.computeFlatTopologicalOrder(reps)
    order
      .filter(o => !o.startsWith("make")) // TODO: remove this to infer make methods as well :)
      .foreach(f => {
        println(s"::::::::::: inferring ${f}")
        val injections = new mutable.HashMap[Injection, Seq[RefoldingStrategy]]()
        //      val engine = SimpleReasoningEngine()
        val engine = ViperReasoningEngine(this.verifier, this.program)
        val mi = MethodInference(
          engine,
          this.defs,
          this.reps,
          this.reps(f),
          new mutable.HashMap(),
          this.methSpec,
          injections
        )
        val beforeSpec = this.methSpec(f)
        val proposed = mi.infer(this.program, this.reps(f), inductionStart = true)
        if(proposed.nonEmpty) {
          println("&".repeat(100))
          println("&".repeat(100))
          println("&".repeat(100))
          val propInj = new mutable.HashMap[Injection, Seq[RefoldingStrategy]]()
          val currentSpec = this.methSpec(f)
          val (pres, posts) = currentSpec
          this.methSpec.put(f, (pres, proposed.map(a => a._2) ++ posts))

          println("ALL ADJUSTED POSTS:")
          (proposed.map(a => a._2) ++ posts).foreach(a => println(a.pretty()))

          val hyp = MethodInference(
            engine,
            this.defs,
            this.reps,
            this.reps(f),
            new mutable.HashMap(),
            this.methSpec,
            propInj
          )
          hyp.infer(this.program, this.reps(f), inductionStart = false)
          println("&".repeat(100))
          println(">".repeat(100))
          println("&".repeat(100))


          println("::::::::::::::::::::: ADJUSTED INDUCTIVE HYPOTHESIS METHOD :::::::::::::::::")
          this.program.methods.filter(m => m.name.equals(f))
            .map(m => {
              val (addPres, addPosts) = this.methSpec(f)
              val extPres = m.pres ++ addPres.map(_.toExp())
              val extPosts = m.posts ++ addPosts.map(_.toExp())
              val injectedBody = injectRefoldingStrategySeqn(propInj.toMap, this.reps(f).body)
              Method(m.name, m.formalArgs, m.formalReturns, extPres, extPosts, Some(injectedBody))()
            })
            .foreach(v => println(v))
        }

        println("::::::::::::::::::::: ADD. SPEC. BEFORE INFERENCE :::::::::::::::::")
        printSpec(beforeSpec)
        println("::::::::::::::::::::: ADD. SPEC. AFTER INFERENCE :::::::::::::::::")
        val afterSpec = this.methSpec(f)
        printSpec(afterSpec)
        println("::::::::::::::::::::: STORIES AT INJECTION :::::::::::::::::")
        mi.injections.toSeq
          .filter(i => i._1 != null)
          .sortBy(e => e._1.id)
          .foreach(e => {
            println(s"injection ${e._1.id}")
            e._2.foreach(v => {
              println(v.pretty())
              println("---")
            })
          })
        println("::::::::::::::::::::: ADJUSTED METHOD :::::::::::::::::")
        this.program.methods.filter(m => m.name.equals(f))
          .map(m => {
            val (addPres, addPosts) = this.methSpec(f)
            val extPres = m.pres ++ addPres.map(_.toExp())
            val extPosts = m.posts ++ addPosts.map(_.toExp())
            val injectedBody = injectRefoldingStrategySeqn(injections.toMap, this.reps(f).body)
            Method(m.name, m.formalArgs, m.formalReturns, extPres, extPosts, Some(injectedBody))()
          })
          .foreach(v => println(v))
      })

    println("::::::::::::::::::::: FULL ADD. SPEC. :::::::::::::::::")
    this.methSpec.foreach(e => {
      println(s"==== ${e._1} ====")
      printSpec(e._2)
    })
  }
}
// TODO: the generated contract for the make method is not complete and leaves the parts about the predicate (e.g. List(this) out)

object MagicWanderWonder {

}