package viper.silver.ast

import viper.silver.parser.{PAccAssertion, PAccPred, PAnnotatedExp, PAnnotatedStmt, PApplyWand, PApplying, PAssert, PAsserting, PAssign, PAssume, PBinExp, PBinder, PBoolLit, PCall, PConstantLiteral, PCurPerm, PDebugLabelledOldExp, PDefine, PDefineBody, PDefineInner, PDelimited, PElse, PEpsilon, PExhale, PExists, PExp, PFieldAccess, PFold, PForPerm, PForall, PFullPerm, PGoto, PGrouped, PHeapOpApp, PIdnUseExp, PIf, PIfContinuation, PInhale, PInhaleExhaleExp, PIntLit, PKw, PLabel, PLet, PLetNestedScope, PLocationAccess, PMacroSeqn, PMagicWandExp, PMakeExp, PMaybePairArgument, PNewExp, PNoPerm, PNullLit, POldExp, POpApp, PPackageWand, PPredCall, PQuantifier, PQuasihavoc, PQuasihavocall, PReserved, PResourceAccess, PResultLit, PSeqn, PSimpleLiteral, PSkip, PSpecification, PSpecs, PStmt, PSym, PType, PTypeSubstitution, PUnfold, PUnfolding, PVars, PVersionedIdnUseExp, PWhile, PWildcard}
import viper.silver.plugin.sif.{PLowEventExp, PLowExp, PRelExp}
import viper.silver.plugin.standard.adt.{PAdtOpApp, PConstructorCall, PDestructorCall, PDiscriminatorCall}
import viper.silver.plugin.standard.predicateinstance.PPredicateInstance
import viper.silver.plugin.standard.refute.PRefute
import viper.silver.plugin.standard.smoke.PUnreachable
import viper.silver.plugin.standard.termination.{PDecreasesClause, PDecreasesStar, PDecreasesTuple, PDecreasesWildcard}

import scala.collection.Set

object ParameterSubstitutor {
  def processParametersExp(exp: PExp, ts: PTypeSubstitution): PExp = {
    println(s"processing ${exp.pretty}")
    val res = exp match {
      case assertion: PAccAssertion => assertion match {
        case p@PPredCall(idnref, typVars, callArgs) => {
          println(s"PreadCall here....")
          val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
          PPredCall(idnref, typVars, updatedArgs)(p.pos)
        }
        case p@PCall(idnref, callArgs, typeAnnotated) => {
          println(s"PCall here....")
          val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
          PCall(idnref, updatedArgs, typeAnnotated)(p.pos)
        }
        case p@PAccPred(op, amount) => {
          println(s"PAccPred here.... ${amount}")
          val internal: PMaybePairArgument[PLocationAccess, PExp] = PMaybePairArgument(
            processParametersLocationAccess(amount.inner.first, ts),
            amount.inner.second.map(a => (a._1, processParametersExp(a._2, ts))))(amount.inner.pos)
          val updatedAmount: PGrouped.Paren[PMaybePairArgument[PLocationAccess, PExp]] = amount.update(internal)
          PAccPred(op, updatedAmount)(p.pos)
        }
        case p@PMakeExp(keyword, constTyp, callArgs) => {
          val updatedType = constTyp.substitute(ts)
          val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
          PMakeExp(keyword, updatedType, updatedArgs)(p.pos)
        }
      }
      case p@PAnnotatedExp(annotation, e) => PAnnotatedExp(annotation, processParametersExp(e, ts))(p.pos)
      case binder: PBinder => binder match {
        case quantifier: PQuantifier => quantifier match {
          case p@PExists(keyword, vars, c, triggers, body) => {
            val updatedBody = processParametersExp(body, ts)
            PExists(keyword, vars, c, triggers, updatedBody)(p.pos)
          }
          case p@PForall(keyword, vars, c, triggers, body) => {
            val updatedBody = processParametersExp(body, ts)
            PForall(keyword, vars, c, triggers, updatedBody)(p.pos)
          }
          case p@PForPerm(keyword, vars, trigger, c, body) => {
            val updatedBody = processParametersExp(body, ts)
            PForPerm(keyword, vars, trigger, c, updatedBody)(p.pos)
          }
        }
      }
      case clause: PDecreasesClause => clause match {
        case p@PDecreasesTuple(tuple, condition) => {
          val updatedTuple: PDelimited[PExp, PSym.Comma] = tuple.update(tuple.inner.map(e => processParametersExp(e._2, ts)))
          val updatedCondition = condition.map(v => (v._1, processParametersExp(v._2, ts)))
          PDecreasesTuple(updatedTuple, updatedCondition)(p.pos)
        }
        case p@PDecreasesWildcard(wildcard, condition) => {
          val updatedCondition = condition.map(v => (v._1, processParametersExp(v._2, ts)))
          PDecreasesWildcard(wildcard, updatedCondition)(p.pos)
        }
        case p@PDecreasesStar(star) => PDecreasesStar(star)(p.pos)
      }
      //case viper.silver.plugin.ParserPluginTemplate.PExampleExp() =>
      case p@PIdnUseExp(idnref) => PIdnUseExp(idnref)
      case p@PLet(l, variable, eq, exp, in, nestedScope) => {
        val updatedExp = exp.update(processParametersExp(exp.inner, ts))
        val updatedBody = processParametersExp(nestedScope.body, ts)
        val updatedNestedScope = PLetNestedScope(updatedBody)(nestedScope.pos)
        PLet(l, variable, eq, updatedExp, in, updatedNestedScope)(p.pos)
      }
      case p@PLowEventExp() => PLowEventExp()(p.pos)
      case p@PLowExp(e) => {
        val updatedExp = processParametersExp(e, ts)
        PLowExp(updatedExp)(p.pos)
      }
      case p@PNewExp(keyword, fields) => PNewExp(keyword, fields)(p.pos)
      case app: POpApp => app match {
        case app: PAdtOpApp => app match {
          case p@PConstructorCall(idnref, callArgs, typeAnnotated) => {
            // TODO CFG: check if type annotated
            val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
            PConstructorCall(idnref, updatedArgs, typeAnnotated)(p.pos)
          }
          case p@PDestructorCall(rcv, dot, idnref) => {
            val updatedExp = processParametersExp(rcv, ts)
            PDestructorCall(updatedExp, dot, idnref)(p.pos)
          }
          case p@PDiscriminatorCall(rcv, dot, is, idnref) => {
            val updatedExp = processParametersExp(rcv, ts)
            PDiscriminatorCall(updatedExp, dot, is, idnref)(p.pos)
          }
        }
        case exp: PBinExp => exp match {
          case p@PMagicWandExp(left, wand, right) => {
            val updatedLeft = processParametersExp(left, ts)
            val updatedRight = processParametersExp(right, ts)
            PMagicWandExp(updatedLeft, wand, updatedRight)(p.pos)
          }
          case _ => {
            val updatedLeft = processParametersExp(exp.left, ts)
            val updatedRight = processParametersExp(exp.right, ts)
            PBinExp(updatedLeft, exp.op, updatedRight)(exp.pos)
          }
        }
        //        case keyword: PCallKeyword => ???
        //        case like: PCallLike => ???
        //        case PCondExp(cond, q, thn, c, els) => ???
        case app: PHeapOpApp => app match {
          case access: PResourceAccess => access match {
            case p@PMagicWandExp(left, wand, right) => {
              val updatedLeft = processParametersExp(left, ts)
              val updatedRight = processParametersExp(right, ts)
              PMagicWandExp(updatedLeft, wand, updatedRight)(p.pos)
            }
            case access: PLocationAccess => processParametersLocationAccess(access, ts)
          }
          case PUnfolding(unfolding, acc, in, exp) => ???
          case PApplying(applying, wand, in, exp) => ???
          case PAsserting(asserting, a, in, exp) => ???
          case PInhaleExhaleExp(l, in, c, ex, r) => ???
          case PCurPerm(op, res) => ???
          case POldExp(op, label, e) => ???
          case PDebugLabelledOldExp(op, label, e) => ???
        }
        //        case PLookup(base, l, idx, r) => ???
        //        case PMapDomain(keyword, base) => ???
        //        case literal: PMapLiteral => ???
        //        case PMapRange(keyword, base) => ???
        //        case PMaplet(key, a, value) => ???
        //        case PRangeSeq(l, low, ds, high, r) => ???
        //        case PSeqSlice(seq, l, s, d, e, r) => ???
        //        case PSize(l, seq, r) => ???
        //        case PUnExp(op, exp) => ???
        //        case PUpdate(base, l, key, a, value, r) => ???
        case p@PFieldAccess(rcv, dot, idnref) => {
          val updatedExp = processParametersExp(rcv, ts)
          PFieldAccess(updatedExp, dot, idnref)(p.pos)
        }
        case e => {
          println(s"UNKNOWN APPLICATION: ${e}")
          throw new IllegalArgumentException(s"Unknown application expression to process generic parameters! ${e.pretty}")
        }
      }
      case p@PPredicateInstance(m, idnuse, args) => {
        val updatedArgs = args.update(args.inner.toSeq.map(e => processParametersExp(e, ts)))
        PPredicateInstance(m, idnuse, updatedArgs)(p.pos)
      }
      case p@PRelExp(e, i) => PRelExp(e, i)(e.pos)
      case literal: PSimpleLiteral => literal match {
        case literal: PConstantLiteral => literal match {
          case l@PBoolLit(keyword) => PBoolLit(keyword)(l.pos)
          case l@PNullLit(keyword) => PNullLit(keyword)(l.pos)
          case l@PNoPerm(keyword) => PNoPerm(keyword)(l.pos)
          case l@PFullPerm(keyword) => PFullPerm(keyword)(l.pos)
          case l@PWildcard(keyword) => PWildcard(keyword)(l.pos)
          case l@PEpsilon(keyword) => PEpsilon(keyword)(l.pos)
        }
        case l@PIntLit(i) => PIntLit(i)(l.pos)
        case l@PResultLit(result) => PResultLit(result)(l.pos)
      }
      case p@PVersionedIdnUseExp(name, version, separator) => PVersionedIdnUseExp(name, version, separator)(p.pos)
      case e => {
        throw new IllegalArgumentException(s"Unknown expression to process generic parameters! ${e.pretty}")
      }
    }
    res.typ = exp.typ.substitute(ts)
    res
  }

  def processParametersLocationAccess(acc: PLocationAccess, ts: PTypeSubstitution): PLocationAccess = {
    acc match {
      case p@PCall(idnref, callArgs, typeAnnotated) => {
        val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
        PCall(idnref, updatedArgs, typeAnnotated)(p.pos)
      }
      case p@PConstructorCall(idnref, callArgs, typeAnnotated) => {
        val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
        PConstructorCall(idnref, updatedArgs, typeAnnotated)(p.pos)
      }
      case p@PFieldAccess(rcv, dot, idnref) => {
        val updatedExp = processParametersExp(rcv, ts)
        PFieldAccess(updatedExp, dot, idnref)(p.pos)
      }
      case p@PMakeExp(keyword, constTyp, callArgs) => {
        val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
        val updatedType = constTyp.substitute(ts)
        PMakeExp(keyword, updatedType, updatedArgs)(p.pos)
      }
      case p@PPredCall(idnref, params, callArgs) => {
        val updatedParams: Option[PGrouped[PSym.Bracket, PDelimited[PType, PReserved[PSym.Comma.type]]]] = params match {
          case Some(value) => {
            val result = value.update(value.inner.toSeq.map(v => v.substitute(ts)))
            Some(result)
          }
          case None => None
        }
        val updatedArgs = callArgs.update(callArgs.inner.toSeq.map(e => processParametersExp(e, ts)))
        PPredCall(idnref, updatedParams, updatedArgs)(p.pos)
      }
      case e => {
        println(s"UNKNOWN APPLICATION: ${e}")
        throw new IllegalArgumentException(s"Unknown application expression to process generic parameters! ${e.pretty}")
      }
    }
  }


  def processParametersSeqn(seq: PSeqn, ts: PTypeSubstitution): PSeqn = {
    PSeqn(seq.ss.update(seq.ss.inner.toSeq.map(v => processParametersStmt(v, ts))))(seq.pos)
  }

  def processParametersElse(els: PElse, ts: PTypeSubstitution): PElse = {
    PElse(els.k, processParametersSeqn(els.els, ts))(els.pos)
  }

  def processParametersIf(ii: PIf, ts: PTypeSubstitution): PIf = {

    val updatedExp = ii.cond.update(processParametersExp(ii.cond.inner, ts))
    val updatedThn = processParametersSeqn(ii.thn, ts)
    val updatedCont = ii.els.map(c => processIfContinuation(c, ts))
    PIf(ii.keyword, updatedExp, updatedThn, updatedCont)(ii.pos)
  }

  def processIfContinuation(cont: PIfContinuation, ts: PTypeSubstitution): PIfContinuation = {
    cont match {
      case i: PIf => processParametersIf(i, ts)
      case i: PElse => processParametersElse(i, ts)
    }
  }

  def processInvsSpec(v: PSpecification[PKw.InvSpec], ts: PTypeSubstitution): PSpecification[PKw.InvSpec] = {
    val updatedExp = processParametersExp(v.e, ts)
    PSpecification[PKw.InvSpec](v.k, updatedExp)(v.pos)
  }

  def processInvsSpecs(v: PSpecs[PKw.InvSpec] , ts: PTypeSubstitution): PSpecs[PKw.InvSpec] = {
    val updatedSpecs = v.specs.update(v.specs.toSeq.map(v => processInvsSpec(v, ts)))
    PSpecs[PKw.InvSpec](updatedSpecs)(v.pos)
  }

  def processParametersStmt(stmt: PStmt, ts: PTypeSubstitution): PStmt = {
    stmt match {
      case continuation: PIfContinuation => processIfContinuation(continuation, ts)
      case p@PAnnotatedStmt(annotation, s) => {
        val updatedStmt = processParametersStmt(s, ts)
        PAnnotatedStmt(annotation, updatedStmt)(p.pos)
      }
      case p@PApplyWand(apply, e) => {
        val updatedExp = processParametersExp(e, ts)
        PApplyWand(apply, updatedExp)(p.pos)
      }
      case p@PAssert(assert, e) => {
        val updatedExp = processParametersExp(e, ts)
        PAssert(assert, updatedExp)(p.pos)
      }
      case p@PAssign(targets, op, rhs) => {
        val updatedRhs = processParametersExp(rhs, ts)
        // TODO CFG: update the targets of the assignment
        PAssign(targets, op, updatedRhs)(p.pos)
      }
      case p@PAssume(assume, e) => {
        val updatedExp = processParametersExp(e, ts)
        PAssume(assume, updatedExp)(p.pos)
      }
      case p@PDefine(annotations, define, idndef, parameters, inner) => {

        val updatedBody: PDefineBody = inner.seqnOrExp match {
          case exp: PExp => processParametersExp(exp, ts)
          case seq: PSeqn => processParametersSeqn(seq, ts)
          case e => {
            throw new IllegalArgumentException(s"Unknown expression to process generic parameters! ${e.pretty}")
          }
        }
        val updatedInner: PDefineInner = PDefineInner(updatedBody)
        PDefine(annotations, define, idndef, parameters, inner)(p.pos)
      }
      case p@PExhale(exhale, e) => {
        val updatedExp = processParametersExp(e, ts)
        PExhale(exhale, updatedExp)(p.pos)
      }
      case p@PFold(fold, e) => {
        val updatedExp = processParametersExp(e, ts)
        PFold(fold, updatedExp)(p.pos)
      }
      case p@PGoto(goto, target) => {
        PGoto(goto, target)(p.pos)
      }
      case p@PInhale(inhale, e) => {
        val updatedExp = processParametersExp(e, ts)
        PInhale(inhale, updatedExp)(p.pos)
      }
      case p@PLabel(label, idndef, invs) => {
        val updatedInvsSpec = invs.update(invs.toSeq.map(v => processInvsSpec(v, ts)))
        PLabel(label, idndef, updatedInvsSpec)(p.pos)
      }
      case p@PMacroSeqn(ss) => {
        val updatedSeq = ss.update(ss.inner.toSeq.map(s => processParametersStmt(s, ts)))
        PMacroSeqn(updatedSeq)(p.pos)
      }
      case p@PPackageWand(pckg, e, proofScript) => {
        val updatedExp = processParametersExp(e, ts)
        val updatedProofScript = proofScript.map(v => processParametersSeqn(v, ts))
        PPackageWand(pckg, updatedExp, updatedProofScript)(p.pos)
      }
      case p@PQuasihavoc(quasihavoc, lhs, e) => {
        val updatedLhs = lhs.map(a => (processParametersExp(a._1, ts), a._2))
        val updatedExp = processParametersExp(e, ts)
        PQuasihavoc(quasihavoc, updatedLhs, updatedExp)(p.pos)
      }
      case p@PQuasihavocall(quasihavocall, vars, colons, lhs, e) => {
        val updatedLhs = lhs.map(a => (processParametersExp(a._1, ts), a._2))
        val updatedExp = processParametersExp(e, ts)
        PQuasihavocall(quasihavocall, vars, colons, updatedLhs, updatedExp)(p.pos)
      }
      case p@PRefute(refute, e) => {
        val updatedExp = processParametersExp(e, ts)
        PRefute(refute, updatedExp)(p.pos)
      }
      case p: PSeqn => processParametersSeqn(p, ts)
      case p@PSkip() => {
        PSkip()(p.pos)
      }
      case p@PUnfold(unfold, e) => {
        val updatedExp = processParametersExp(e, ts)
        PUnfold(unfold, updatedExp)(p.pos)
      }
      case p@PUnreachable(kw) => {
        PUnreachable(kw)(p.pos)
      }
      case p@PVars(keyword, vars, init) => {
        val updatedInit = init.map(a => (a._1, processParametersExp(a._2, ts)))
        PVars(keyword, vars, updatedInit)(p.pos)
      }
      case p@PWhile(keyword, cond, invs, body) => {
        val updatedCond = cond.update(processParametersExp(cond.inner, ts))
        val updatedInvs = processInvsSpecs(invs, ts)
        val updatedBody = processParametersSeqn(body, ts)
        PWhile(keyword, updatedCond, updatedInvs, updatedBody)(p.pos)
      }
      case e => {
        throw new IllegalArgumentException(s"Unknown statement to process generic parameters! ${e.pretty}")
      }
    }
  }
}
