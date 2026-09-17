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

  def attemptMagicWandConstruction(kb: KnowledgeBase, pred: PredInstAccTerm): Unit = {
    println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%")
    val predDef = this.defs(pred.pred.name)
    val body = predDef.instantiate(pred.pred)
    // locate the stuff that is not satisfied yet
    // TODO: extend the refolding strategy to include
    //              package: sub parts are the steps required to package this magic wand
    //              apply: single argument which contains a magic wand
    //           maybe use the verifier to get information about the parts that are not satisfied yet?
    //           maybe just check from the current scope and call "findRefoldingStrategy" + checking the pure info (or leave that out and say its a heuristic?!)


    // TODO: maybe extend with potential and pure parts
    val rawFolded = PredicateCollector.collectFoldedPredicates(this.engine, body, kb)
    val rawDirect = PredicateCollector.collectDirectPredicates(this.engine, body, kb)
//    val rawStripped = PredicateCollector.stripToPure(this.engine, body, kb)
//    val rawPartial = PredicateCollector.collectPotSatImpls(this.eng ine, body, kb)

    val (kb1, folded) = normalizeFoldedRequirements(kb, rawFolded)
    val (kb2, direct) = normalizeDirectRequirements(kb1, rawDirect)

    println(s"Folded Requirements: ${folded.map(_.pretty()).mkString("   &   ")}")
    println(s"Direct Requirements: ${direct.map(_.pretty()).mkString("   &   ")}")
    println("Knowledge Base:")
    println(kb2.pretty())
//    val (kb3, stripped) = normalizeLogicTerm(kb2, rawStripped)
//    val (kb4, partial) = normalizePotentialRequirements(kb3, rawPartial)

//    println("CHECKING FOLDED:")
    val missingFolded = folded.filter(f => kb2.findRefoldingStrategy(this.engine, this.defs, f).isEmpty)
    val missingDirect = direct.filter(d => kb2.findUnfoldingStrategy(this.engine, this.defs, d).isEmpty)

    println(s"missing folded: ${missingFolded.map(_.pretty()).mkString(" & ")}")
    println(s"missing direct: ${missingDirect.map(_.pretty()).mkString(" & ")}")
    println("")
    val bm = kb2.constructInfoBackMapping()
    println(s"missing folded bm: ${missingFolded.map(v => applyBm(bm, v)).map(_.pretty()).mkString(" & ")}")
    println(s"missing direct bm: ${missingDirect.map(v => applyBm(bm, v)).map(_.pretty()).mkString(" & ")}")
    println("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%")

    /*
      TODO: add injection point at the last position in if branches to allow different injections to take place on different paths
          e.g.
          if(x == null)
          {
            ....
            injection 1
          }
          else
          {
            ....
            if(something)
            {
              injection 2
            }
            else
            {
              injection 3
            }
            injection 4 -> only chose this when there is something other than a merge line before this path
          }

          when reconstructing the magic wand choose the injection corresponding to the path that it has come from (hope that its localized enough :) )
    */
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

  private def applyRefoldingStep(engine: ReasoningEngine, base: KnowledgeBase, step: RefoldingStep): KnowledgeBase = {
    step match {
      case FoldingStep(pred, perm) => {
        // if in the future the folding step has sub steps to fold other stuff beforehand then
        // insert the folding here before folding self

        // fold self
        base.fold(engine, this.defs, pred, perm)
      }
      case UnfoldingStep(pred, perm, subs) => {
        // unfold the predicate on the current level
        val unfolded = base.unfold(engine, this.defs, pred, perm)
        // unfold all the steps within this predicate
        // the substeps are scaled by the amount that the current unfolding actually unfolded
        subs.map(s => s.scale(perm))
          .foldLeft(unfolded)((a, b) => applyRefoldingStep(engine, a, b))
      }
      case c => {
        throw new IllegalArgumentException(s"Unable to process refolding step type ${c.getClass.getCanonicalName}")
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
    strat.steps.foldLeft(before)((a, b) => applyRefoldingStep(engine, a, b))
  }

  private def applyStrategies(engine: ReasoningEngine, inj: Injection, before: KnowledgeBase, strats: Seq[RefoldingStrategy]): KnowledgeBase = {
    strats.foldLeft(before)((kb, s) => applyRefoldingStrategy(engine, inj, kb, s))
  }

  private def propagateBackFieldPermReq(from: Ident, pred: PredFieldAccTerm, actual: Term): Boolean = {
    // TODO: fix the shortcut and actually propagate the requirements backward
    println(s"PROPAGATING BACK: ${pred.pretty()} has only ${actual.pretty()} from ${from}")
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

  def processLine(before: KnowledgeBase, line: Line): (Boolean, KnowledgeBase) = {
    line match {
      case BranchLine(ln, pre, cond, thn, els) => {
        (false, before)
      }
      case MergeLine(ln, cb, thn, els, lthn, lels) => {
        (false, before)
      }
      case AssertLine(ln, inj, exp) => {
        clearInjection(inj)

        // collecting the fields that are accessed within this
        val rawAccessPermissions = collectRequiredFieldPermissions(exp)
        val (normFields, accessPermissions) = normalizeDirectRequirements(before, rawAccessPermissions.toSeq)

        println(s"RAW ACCESSED FIELDS: ${rawAccessPermissions.map(_.pretty())}")
        println(s"NORMED ACCESSED FIELDS: ${accessPermissions.map(_.pretty())}")

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

          val (kb1, folded) = normalizeFoldedRequirements(refolding, rawFolded)
          val (kb2, direct) = normalizeDirectRequirements(kb1, rawDirect)
          val (kb3, stripped) = normalizeLogicTerm(kb2, rawStripped)
          val (kb4, partial) = normalizePotentialRequirements(kb3, rawPartial)

          println(s"RAW DIRECT: ${rawDirect}")
          println(s"NORMED DIRECT: ${direct}")

          direct.foreach(d => {
            println(s"::::::::::::::::::::::::::::::::::::::")
            println(s"CHECKING FRO DIRECT PREDICATE EXISTENCE: ${d}")
            this.engine.prove(kb4, d)
            println(s"::::::::::::::::::::::::::::::::::::::")
          })

          println(s"::::::::::::::::::::::::::::::::::::::")
          println(s"CHECKING FOR STRIPPED: ${stripped.pretty()}")
          this.engine.prove(kb4, stripped)
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
      case AssumeLine(ln, exp) => {
        val stripped = PredicateCollector.stripToPure(this.engine, exp, before)
        val resKb = before.update(a => h => d => f => i => {
          (a, h, d, f, i.and(stripped))
        })
        val cleanedKb = cleanPotentialWithCurrentKnowledge(resKb)
        (false, cleanedKb)
      }
        //      case BranchLine(ln, pre, cond, thn, els) =>
      case CallLine(ln, inj, method, targets, args) => {
        // TODO: include framing rule by checking if field access is retained
        val initial = this.reps(method)
        val spec = this.methSpec(method)

        // exhale the pres in reverse order
        val extendedPres = initial.pres ++ spec._1
        val (shouldRestart, afterExhales) = extendedPres.reverse.foldLeft((false, before))((acc, p) => {
          val (r, kb) = acc
          val strats = getRefoldingStrategiesAtInjectionPoint(inj)
          val (restart, result) = processLine(kb, ExhaleLine(ln, inj, p))
          val after = getRefoldingStrategiesAtInjectionPoint(inj)
          clearInjection(inj)
          addRefoldingStrategiesToInjectionPoint(inj, strats ++ after)
          (r || restart, result)
        })
        if (shouldRestart) {
          (true, afterExhales)
        }
        else {

          // inhale the posts in correct order
          val extendedPosts = initial.posts ++ spec._2
          // TODO: fix restart flag stuff
          val afterInhales = extendedPosts.foldLeft(afterExhales)((kb, p) => processLine(kb, InhaleLine(ln, p))._2)

          (false, afterInhales)
        }
      }
      case ExhaleLine(ln, inj, exp) => {
        clearInjection(inj)

        // TODO: check that all requirements are satisfied i.e. that all the field/pred permissions are provided
        //       -> generate and apply refolding strategies
        val folded = PredicateCollector.collectFoldedPredicates(this.engine, exp, before)
        val direct = PredicateCollector.collectDirectPredicates(this.engine, exp, before)
        val stripped = PredicateCollector.stripToPure(this.engine, exp, before)
        println(s"CHECKING EXHALE ${exp.pretty()} WITH: ${folded}")

        val afterUnfolding = direct.foldLeft(before)((kb, d) => {
          kb.findUnfoldingStrategy(this.engine, this.defs, d)
            .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
            .getOrElse(kb)
        })

        val afterRefolding = folded.foldLeft(afterUnfolding)((kb, f) => {
          kb.findRefoldingStrategy(this.engine, this.defs, f)
            .map(s => applyRefoldingStrategy(this.engine, inj, kb, s))
            .getOrElse(kb)
        })

        // TODO: detect that the predicate permissions are not fulfilled

        val resKb = afterRefolding.update(a => h => d => f => fac => {
          val ud = direct.foldLeft(d)((a, b) => a.exhale(b))
          val uf = folded.foldLeft(f)((a, b) => a.exhale(b))
          val ufac = fac.and(stripped)
          (a, h, ud, uf, ufac)
        })

        (false, resKb)
      }
      case LocalAssignLine(ln, inj, variable, value) => {
        clearInjection(inj)

        val rawReqsValue = collectRequiredFieldPermissions(value)
        val (resNormKb, reqsValue) = normalizeDirectRequirements(before, rawReqsValue.toSeq)
        //        val stratsValue = reqsValue.map(v => (v, before.findUnfoldingStrategy(this.defs, v)))
        //          .flatMap(v => v._2).toSeq
        //        val kb = applyStrategies(inj, before, stratsValue)

        // TODO: copy this part to the field assign
        val kb = reqsValue.foldLeft(resNormKb)((k, r) => {
          val strat = k.findUnfoldingStrategy(this.engine, this.defs, r)
          strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
        })

        reqsValue.map(p => (p, kb.direct.getAmount(p.exp)))
          .filter(p => !kb.hasEnoughPermissions(this.engine, p._1.perm, p._2))
          .foreach(p => propagateBackFieldPermReq(ln, p._1, p._2))

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
      case FieldAssignLine(ln, inj, fa, value) => {
        clearInjection(inj)

        val reqs = collectRequiredFieldPermissions(fa.src)
        val self = Set(PredFieldAccTerm(fa, PermFracTerm(IntTerm(1), IntTerm(1))))

        // TODO: this can be improved by first searching for all strategies and then deciding which strategies should be executed
        //       -> iteratively improve current standing until final state reached
        val combinedRaw = reqs.union(self)

        val (kbNormTarget, combined) = normalizeDirectRequirements(before, combinedRaw.toSeq)
        val kbAfterTarget = combined.foldLeft(kbNormTarget)((k, r) => {
          val strat = k.findUnfoldingStrategy(this.engine, this.defs, r)
          strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
        })

        val reqsValueRaw = collectRequiredFieldPermissions(value)
        val (kbNormValue, reqsValue) = normalizeDirectRequirements(kbAfterTarget, reqsValueRaw.toSeq)
        val kbAfterValue = reqsValue.foldLeft(kbNormValue)((k, r) => {
          val strat = k.findUnfoldingStrategy(this.engine, this.defs, r)
          strat.map(s => applyStrategies(this.engine, inj, k, Seq(s))).getOrElse(k)
        })

        // TODO: add normalization to the other parts which have stuff collected

        val kb = kbAfterValue

        val stillMissingValue = reqsValue.map(p => (p, kb.direct.getAmount(p.exp)))
          .filter(p => !kb.hasEnoughPermissions(this.engine, p._1.perm, p._2))

        val someSuccessWithPotential = stillMissingValue.map(a => findIfPotHasSolution(ln, kb, a._1, a._2))
          .exists(a => a)

        if (someSuccessWithPotential) {
          (true, kb)
        }
        else {
          val someSuccessWithDirectPropVal = stillMissingValue.map(p => propagateBackFieldPermReq(ln, p._1, p._2))
            .exists(a => a)
          if (someSuccessWithDirectPropVal) {
            (true, kb)
          }
          else {
            val stillMissingTarget = combined.map(p => (p, kb.direct.getAmount(p.exp)))
              .filter(p => !kb.hasEnoughPermissions(this.engine, p._1.perm, p._2))

            val someSuccessWithPotTarget = stillMissingTarget.map(a => findIfPotHasSolution(ln, kb, a._1, a._2)).exists(a => a)
            if (someSuccessWithPotTarget) {
              (true, kb)
            }
            else {
              println(s"STILL MISSING FOR TARGET: ${stillMissingTarget}")
              stillMissingTarget.foreach(m => {
                searchForPermissionFieldAdjustmentToGetPermissions(kb, m._1, m._2)
              })

              val someSuccessWithDirectPropTarget = stillMissingTarget.map(p => propagateBackFieldPermReq(ln, p._1, p._2))
                .exists(a => a)

              if (someSuccessWithDirectPropTarget) {
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

          }
        }

      }
      case InhaleLine(ln, exp) => {
        val rawFolded = PredicateCollector.collectFoldedPredicates(this.engine, exp, before)
        val rawDirect = PredicateCollector.collectDirectPredicates(this.engine, exp, before)
        val rawStripped = PredicateCollector.stripToPure(this.engine, exp, before)
        val rawPartial = PredicateCollector.collectPotSatImpls(this.engine, exp, before)
        val rawMagic = PredicateCollector.collectBaguettes(this.engine, exp, before)

        val (kb1, folded) = normalizeFoldedRequirements(before, rawFolded)
        val (kb2, direct) = normalizeDirectRequirements(kb1, rawDirect)
        val (kb3, stripped) = normalizeLogicTerm(kb2, rawStripped)
        val (kb33, partial) = normalizePotentialRequirements(kb3, rawPartial)
        val (kb4, baguettes) = normalizeBaguetteRequirements(kb33, rawMagic)


        // TODO: normalize the folded, direct, partial and stripped (EVERYWHERE)
        val resKb = kb4.update((a, h, d, f, fac, pot, mag) => {
          val ud = direct.foldLeft(d)((a, b) => a.inhale(b))
          val uf = folded.foldLeft(f)((a, b) => a.inhale(b))
          val ufac = fac.and(stripped)
          val up = pot.inhale(partial)
          val um = baguettes.foldLeft(mag)((a, b) => a.addWand(b))
          (a, h, ud, uf, ufac, up, um)
        })

        val cleanedKb = cleanPotentialWithCurrentKnowledge(resKb)

        (false, cleanedKb)
      }
      case NewObjLine(ln, target, fields) => {
        // perform the assignment
        val (a2, refBeforeAssign) = before.assignment.lookup(target.name, target.typ)
        val valRef = a2.rc.freshValRef()
        val ua = a2.assign(target.name, valRef, target.typ)

        val afterAssign = KnowledgeBase(
          before.path, ua, before.heap, before.direct, before.folded, before.info, before.partial, before.mwm, before.fieldTypes
        )

        // substitute the old variable and inhale the new permissions
        val ts = MapTermSub(Map((target, VarTerm(s"t$$${refBeforeAssign.id}", target.typ))))
        val resKb = afterAssign.update(
          a => h => d => f => i => {
            val dir = fields.foldLeft(d.substitute(ts))((m, f) => {
              val fa = FieldAccTerm(target, f._1, f._2)
              m.inhale(PredFieldAccTerm(fa, PermAmount.WRITE))
            })
            val fol = f.substitute(ts)
            val info = i.substitute(ts).asInstanceOf[LogicTerm].and(NotEqCmpTerm(target, NullTerm()))
            (a, h, dir, fol, info)
          }
        )

        (false, resKb)
      }
      case l => {
        throw new IllegalArgumentException(s"Unable to process line type ${l.getClass.getCanonicalName}")
      }
    }
  }

  private def normalizeLogicTerm(before: KnowledgeBase, term: LogicTerm): (KnowledgeBase, LogicTerm) = {
    val (kbT, refT, typT, infoT) = TermNormalization.computeNormalizedLogicTerm(before, before.assignment.rc, term)
    val resKb = kbT.extendInfo(infoT)
    val variable = refT.toVarTerm(typT)
    (resKb, variable)
  }

  private def normalizeTerm(before: KnowledgeBase, term: Term): (KnowledgeBase, Term) = {
    val (kbT, refT, typT, infoT) = TermNormalization.computeNormalizedValueRef(before, before.assignment.rc, term)
    val resKb = kbT.extendInfo(infoT)
    val variable = refT.toVarTerm(typT)
    (resKb, variable)
  }

  private def normalizeTermList(before: KnowledgeBase, terms: Seq[Term]): (KnowledgeBase, Seq[Term]) = {
    terms.foldLeft((before, Seq[Term]()))((acc, t) => {
      val (resKb, variable) = normalizeTerm(acc._1, t)
      (resKb, acc._2 ++ Seq(variable))
    })
  }

  private def normalizeFoldedRequirements(before: KnowledgeBase, reqs: Seq[PredInstAccTerm]): (KnowledgeBase, Seq[PredInstAccTerm]) = {
    reqs.foldLeft((before, Seq[PredInstAccTerm]()))((acc, r) => {
      val (resKb, args) = normalizeTermList(acc._1, r.pred.args)
      val (kb, perm) = normalizeTerm(resKb, r.perm)
      val pred = PredInstAccTerm(PredInst(r.pred.name, args), perm)
      (kb, acc._2 ++ Seq(pred))
    })
  }

  private def normalizeDirectRequirements(before: KnowledgeBase, reqs: Seq[PredFieldAccTerm]): (KnowledgeBase, Seq[PredFieldAccTerm]) = {
    reqs.foldLeft((before, Seq[PredFieldAccTerm]()))((acc, f) => {
      val (resKb, src) = normalizeTerm(acc._1, f.exp.src)
      val (kb, perm) = normalizeTerm(resKb, f.perm)
      val pred = PredFieldAccTerm(
        FieldAccTerm(
          src,
          f.exp.field,
          f.exp.typ
        ),
        perm
      )
      (kb, acc._2 ++ Seq(pred))
    })
  }

  private def normalizeBaguetteRequirements(before: KnowledgeBase, reqs: Seq[BaguetteMagic]): (KnowledgeBase, Seq[BaguetteMagic]) = {
    reqs.foldLeft((before, Seq[BaguetteMagic]()))((acc, f) => {
      val (kb1, dirPrem) = normalizeDirectRequirements(before, f.directPrem.toSeq)
      val (kb2, folPrem) = normalizeFoldedRequirements(kb1, f.foldedPrem.toSeq)
      val (kb3, dirCons) = normalizeDirectRequirements(kb2, f.directCons.toSeq)
      val (kb4, folCons) = normalizeFoldedRequirements(kb3, f.foldedCons.toSeq)

      (kb4, acc._2 ++ Seq(BaguetteMagic(dirPrem.toSet, folPrem.toSet, dirCons.toSet, folCons.toSet)))
    })

  }

  private def normalizePotentialRequirements(before: KnowledgeBase, reqs: Seq[ImplTerm]): (KnowledgeBase, Seq[ImplTerm]) = {
    reqs.foldLeft((before, Seq[ImplTerm]()))((acc, i) => {
      val (kb1, prem) = normalizeLogicTerm(acc._1, i.prem)
      val (kb2, cons) = normalizeLogicTerm(kb1, i.cons)
      val impl = ImplTerm(prem, cons)
      (kb2, acc._2 ++ Seq(impl))
    })
  }

  private def cleanPotentialWithCurrentKnowledge(resKb: KnowledgeBase): KnowledgeBase = {
    val sat = resKb.partial.partial.filter(p => this.engine.prove(resKb, p.prem).equals(Sat))
      .map(p => p.cons)
    val unsat = resKb.partial.partial.filter(p => this.engine.prove(resKb, p.prem).equals(UnSat))
    val potsat = resKb.partial.partial.filter(p => this.engine.prove(resKb, p.prem).equals(PotSat))

    if (sat.isEmpty && unsat.isEmpty) {
      resKb
    }
    else {
      val redPot = resKb.update((a, h, d, f, i, _) => (a, h, d, f, i, Potential(potsat)))
      sat.foldLeft(redPot)((kb, r) => {
        val dirs = PredicateCollector.collectDirectPredicates(this.engine, r, kb)
        val folds = PredicateCollector.collectFoldedPredicates(this.engine, r, kb)
        val pots = PredicateCollector.collectPotSatImpls(this.engine, r, kb)
        val pure = PredicateCollector.stripToPure(this.engine, r, kb)
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

  // TODO: THIS DOES NOT WORK WITH THE CONTINUATION THAT PROVIDES A TERM INSTEAD OF A COMPARISON
  //       -> THINK ABOUT HOW TO SOLVE IT
  //           -> maybe use a second entry in the line propagator that converts a value of generic T to LogicTerm
  //           -> and ContinueAdjustment has also this generic parameter?
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

  private def propagatePureConstraints(ident: Ident, pure: LogicTerm): Boolean = {
    //    if (pure.clauses.size != 1) {
    //      throw new IllegalArgumentException(s"Expected single conjunction but got disjunction of pure terms! ${pure.toLogicTerm().pretty()}")
    //    }

    val preds = this.currentMethod.rep.getPredecessors(ident)
    println(s"ADDITIONAL REQUIREMENTS THAT NEED TO BE PROPAGATED!: ${pure.pretty()}")
    // TODO: think about a better propagation strategy. or just convert the existing information in the
    true
    //    if (preds.size == 1) {
    //      val pred = preds.head
    //      pure.clauses.head.map(p => {
    //          val (lp, pay) = getLinePropagator(p)
    //          val response = propagatePureConstraintThrough(pred, this.currentMethod.start, lp, pay)
    //          response match {
    //            case _: SuccessfulAdjustment[Term] => println(s"Successfully propagated constraint ${p}!")
    //            case _ => println("Unable to propagate constraint!")
    //          }
    //          response
    //        })
    //        .exists(a => a.isInstanceOf[SuccessfulAdjustment[Term]])
    //    }
    //    else {
    //      throw new IllegalArgumentException(s"Expected single predecessor of line got: ${preds.size}")
    //    }
  }

  private def findIfPotHasSolution(current: Ident, kb: KnowledgeBase, target: PredFieldAccTerm, amount: Term): Boolean = {
    val implSearchDepth = 10
    println(s"CHECKING IN IMPLICATIONS FOR: ${target.pretty()}")
    val reqs = kb.partial.partial.toSeq
      .flatMap(a => findRequiredKnowledge(kb, a, target, implSearchDepth))
      .foldLeft(Set[LogicTerm]())((a, b) => a.union(b))

    if (reqs.nonEmpty) {
      // TODO: joining like this would prevent something like: (A ==> REQ)  &  (!A ==> REQ)
      val pure = reqs.map(r => PredicateCollector.stripToPure(this.engine, r, kb))
        .reduceLeftOption((a, b) => a.and(b))
        .getOrElse(BoolTerm(true))
      propagatePureConstraints(current, pure)
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

  def infer(program: Program, meth: InternalMethod) = {
    // generate mapping of field definitions to their corresponding type
    val fieldTypes = program.fields.map(f => f.name -> f.typ).toMap

    this.knowledge.clear()
    val counter = RefCounter(Counter(0))

    val mesh = meth.rep.mesh
    val lines = meth.rep.lines

    var restarting = true
    while (restarting) {
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
            if (lines.contains(i)) {
              lines(i) match {
                case BranchLine(ln, pre, cond, thn, els) => {
                  val assumption = if (thn == current) cond else NotTerm(cond)
                  this.knowledge(i).values
                    .map(k => /* cleanPotentialWithCurrentKnowledge */ (k.withPath(ln, assumption).withInfo(assumption)))
                }
                case _ => this.knowledge(i).values
              }
            } else {
              this.knowledge(i).values
            }
          })

        kbs.foreach(kb => {
          if (!restarting) {
            val line = lines(current)
            println(s"line: ${line.pretty()}")

            val (shouldRestart, after) = processLine(kb, line)
            restarting = shouldRestart


            println(s":::::::::::::::: AFTER ${current.pretty()} :::::::::::::::::")
            println(after.pretty())


            setKnowledgeBase(current, after)

            if(true){
              val rc = RefCounter(Counter(0))
              val kb0 = new KnowledgeBase(after.fieldTypes, rc)
              val rawPart = PredInstAccTerm(PredInst("Part", Seq(VarTerm("x", Ref))), PermAmount.WRITE)
              val (kb1, parts) = normalizeFoldedRequirements(kb0, Seq(rawPart))
              val missing = PredInstAccTerm(PredInst("Missing", Seq(VarTerm("x", Ref))), PermAmount.WRITE)
              val dummy = kb1
                .update((a, h, d, f, i, p) => (a, h, d, f.inhale(parts.head), i, p))
              val desired = PredInstAccTerm(PredInst("Wand", Seq(VarTerm("x", Ref))), PermAmount.WRITE)
              attemptMagicWandConstruction(dummy, desired)
            }

            if (restarting) {
              // TODO: fix the restarting logic
//              println("KB WHEN RESTARTING:")
//              println(after.pretty())
              dumpBeautifiedKbs()
              println("INJECTIONS WHEN RESTARTING:")
              this.injections.foreach(e => {
                println(e._1)
                e._2.foreach(s => println(s.pretty().indent(2)))
              })
              throw new IllegalArgumentException(s"RESTARTING :/ ${line.pretty()}")
            }
          }
        })

        open = open.tail ++ mesh(current).toSeq
      }

      if (!restarting) {

        val startKbs = this.knowledge(meth.start).values
        if (startKbs.size != 1) {
          throw new IllegalArgumentException("Expected a single knowledge base at the start of the method!")
        }
        val startKb = startKbs.head

        val finalKbs = this.knowledge(meth.stop).values

        finalKbs.foreach(finalKb => {
          // TODO: the refolding strategies must match
          // TODO: the injections must be cleared per path/across all paths
          val mergedPosts = (meth.posts ++ this.methSpec(this.currentMethod.method)._2).reverse

          val finInj = this.currentMethod.finalInj

          on(this.engine, startKb, finalKb, meth)

          val afterPosts = mergedPosts.foldLeft(finalKb)((kb, p) => processLine(kb, ExhaleLine(meth.stop, finInj, p))._2)
          //        this.knowledge.put(meth.stop, afterPosts)
          // TODO: extend the post conditions with the information that are left over
        })

      }

      if (true) {
        dumpBeautifiedKbs()
//        dumpRawKbs()
      }
    }
  }

  private def applyBm(bm: TermSub, term: Term): Term = {
    FixedPoint.compute(term, (s: Term) => s.substitute(bm))
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
        if (engine.prove(kb, pred) == Sat) {
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
    println("CHECKING THE STATE AFTER:")
    println(s"IBM: ${initialBackmapping}")
    println(s"BM: ${backmapping}")
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
    order.foreach(f => {
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
      mi.infer(this.program, this.reps(f))
      println("::::::::::::::::::::: ADD. SPEC. BEFORE INFERENCE :::::::::::::::::")
      printSpec(beforeSpec)
      println("::::::::::::::::::::: ADD. SPEC. AFTER INFERENCE :::::::::::::::::")
      val afterSpec = this.methSpec(f)
      printSpec(afterSpec)
      println("::::::::::::::::::::: STORIES AT INJECTION :::::::::::::::::")
      mi.injections.toSeq
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



object MagicWanderWonder
{

}