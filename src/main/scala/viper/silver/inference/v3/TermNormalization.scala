package viper.silver.inference.v3

import viper.silver.ast.{BoolLit, Type}
import viper.silver.inference.v3.ast.{AddTerm, AndTerm, BaguetteMagic, BoolTerm, CondTerm, EqCmpTerm, FieldAccTerm, FieldPermAmountTerm, GreaterCmpTerm, GreaterEqCmpTerm, ImplTerm, IntTerm, LessCmpTerm, LessEqCmpTerm, LogicTerm, MulTerm, NegTerm, NotEqCmpTerm, NotTerm, NullTerm, OrTerm, PermFracTerm, PredFieldAccTerm, PredInst, PredInstAccTerm, SubTerm, Term, VarTerm}
import viper.silver.inference.v3.knowledge.KnowledgeBase

object TermNormalization {

  def computeNormalizedTermList(kb: KnowledgeBase, counter: RefCounter, terms: Seq[Term]): (KnowledgeBase, Seq[Term], LogicTerm) = {
    terms.foldLeft((kb, Seq[Term](), BoolTerm(true).asInstanceOf[LogicTerm]))((acc, t) => {
      val (afterKb, ref, typ, info) = TermNormalization.computeNormalizedValueRef(acc._1, counter, t)
      (afterKb, acc._2 ++ Seq(ref.toVarTerm(typ)), acc._3.and(info))
    })
  }

  private def computeNormalizedBinaryOperator(kb: KnowledgeBase, counter: RefCounter, resType: Type, left: Term, right: Term, op: (Term, Term) => Term): (KnowledgeBase, ValRef, Type, LogicTerm) = {
    val (kbA, refA, typA, infoA) = computeNormalizedValueRef(kb, counter, left)
    val (kbB, refB, typB, infoB) = computeNormalizedValueRef(kbA, counter, right)
    val ref = counter.freshValRef()
    val valRefVar = ref.toVarTerm(resType)
    val valRefVarA = refA.toVarTerm(typA)
    val valRefVarB = refB.toVarTerm(typB)
    (kbB, ref, resType, infoA.and(infoB).and(EqCmpTerm(valRefVar, op(valRefVarA, valRefVarB))))
  }

  private def computeNormalizedBinaryOperatorWithTypeMapping(kb: KnowledgeBase, counter: RefCounter, typeMapping: Map[(Type, Type), Type], left: Term, right: Term, op: (Term, Term) => Term): (KnowledgeBase, ValRef, Type, LogicTerm) = {
    val (kbA, refA, typA, infoA) = computeNormalizedValueRef(kb, counter, left)
    val (kbB, refB, typB, infoB) = computeNormalizedValueRef(kbA, counter, right)
    val ref = counter.freshValRef()
    val resType = typeMapping(typA, typB)
    val valRefVar = ref.toVarTerm(resType)
    val valRefVarA = refA.toVarTerm(typA)
    val valRefVarB = refB.toVarTerm(typB)
    (kbB, ref, resType, infoA.and(infoB).and(EqCmpTerm(valRefVar, op(valRefVarA, valRefVarB))))
  }

  private def computeNormalizedLiteral(kb: KnowledgeBase, counter: RefCounter, resType: Type, lit: Term): (KnowledgeBase, ValRef, Type, LogicTerm) = {
    val ref = counter.freshValRef()
    val valRefVar = ref.toVarTerm(resType)
    (kb, ref, resType, EqCmpTerm(valRefVar, lit))
  }

  private def computeNormalizedUnaryOperator(kb: KnowledgeBase, counter: RefCounter, resType: Type, sub: Term, op: Term => Term): (KnowledgeBase, ValRef, Type, LogicTerm) = {
    val (kbS, refS, typS, infoS) = computeNormalizedValueRef(kb, counter, sub)
    val ref = counter.freshValRef()
    val valRefVar = ref.toVarTerm(resType)
    val valRefVarSub = refS.toVarTerm(typS)
    (kbS, ref, resType, infoS.and(EqCmpTerm(valRefVar, op(valRefVarSub))))
  }

  def computeNormalizedLogicTerm(kb: KnowledgeBase, counter: RefCounter, term: LogicTerm): (KnowledgeBase, ValRef, Type, LogicTerm) = {
    term match {
      case AndTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, (a, b) => AndTerm(a.asInstanceOf[LogicTerm], b.asInstanceOf[LogicTerm]))
      case lit: BoolTerm => computeNormalizedLiteral(kb, counter, viper.silver.ast.Bool, lit)
      case EqCmpTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, EqCmpTerm)
      case GreaterCmpTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, GreaterCmpTerm)
      case GreaterEqCmpTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, GreaterEqCmpTerm)
      case LessCmpTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, LessCmpTerm)
      case LessEqCmpTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, LessEqCmpTerm)
      case NotEqCmpTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, NotEqCmpTerm)
      case NotTerm(t) => computeNormalizedUnaryOperator(kb, counter, viper.silver.ast.Bool, t, v => NotTerm(v.asInstanceOf[LogicTerm]))
      case OrTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, (a, b) => OrTerm(a.asInstanceOf[LogicTerm], b.asInstanceOf[LogicTerm]))
      case VarTerm(name, typ) =>
        val lookupResult = kb.assignment.lookup(name, typ)
        val valRef = lookupResult._2
        val ukb = kb.withAssignment(lookupResult._1)
        (ukb, valRef, typ, BoolTerm(true))
      case c =>
        throw new IllegalArgumentException(s"Unable to compute normalized form for logic term of type ${c.getClass.getCanonicalName}")
    }
  }

  def computeNormalizedValueRef(kb: KnowledgeBase, counter: RefCounter, term: Term): (KnowledgeBase, ValRef, Type, LogicTerm) = {
    term match {
      case FieldAccTerm(src, field, _) =>
        val (kbS, refS, _, infoS) = computeNormalizedValueRef(kb, counter, src)
        val (h, ref) = kbS.heap.lookupField(refS, field)
        val resKb = kbS.withHeap(h)
        (resKb, ref, kb.fieldTypes(field), infoS)
      case AddTerm(a, b) =>
        val intTyp: Type = viper.silver.ast.Int
        val permTyp: Type = viper.silver.ast.Perm
        val mapping = Seq(
          ((intTyp, intTyp), intTyp),
          ((permTyp, permTyp), permTyp)
        ).toMap
        computeNormalizedBinaryOperatorWithTypeMapping(kb, counter, mapping, a, b, AddTerm)
      case lit: IntTerm => computeNormalizedLiteral(kb, counter, viper.silver.ast.Int, lit)
      case lt: LogicTerm => computeNormalizedLogicTerm(kb, counter, lt)
      case MulTerm(a, b) =>
        val mapping: Map[(Type, Type), Type] = Map(
          ((viper.silver.ast.Perm, viper.silver.ast.Perm), viper.silver.ast.Perm),
          ((viper.silver.ast.Int, viper.silver.ast.Perm), viper.silver.ast.Perm),
          ((viper.silver.ast.Perm, viper.silver.ast.Int), viper.silver.ast.Perm),
          ((viper.silver.ast.Int, viper.silver.ast.Int), viper.silver.ast.Int)
        )
        computeNormalizedBinaryOperatorWithTypeMapping(kb, counter, mapping, a, b, MulTerm)
      case NegTerm(t) => computeNormalizedUnaryOperator(kb, counter, viper.silver.ast.Int, t, NegTerm)
      case lit: NullTerm => computeNormalizedLiteral(kb, counter, viper.silver.ast.Ref, lit)
      case PermFracTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Perm, a, b, PermFracTerm)
      case SubTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Int, a, b, SubTerm)
      case c =>
        throw new IllegalArgumentException(s"Unable to compute normalized form for term of type ${c.getClass.getCanonicalName}")
    }
  }

  def normalizeMutablePartsInTermList(kb: KnowledgeBase, terms: Seq[Term]): (KnowledgeBase, Seq[Term]) = {
    terms.foldLeft((kb, Seq[Term]()))((acc, t) => {
      val (normKb, normTerm) = normalizeMutablePartsInTerm(acc._1, t)
      (normKb, acc._2 ++ Seq(normTerm))
    })
  }

  def normalizeMutablePartsInDirect(kb: KnowledgeBase, direct: PredFieldAccTerm): (KnowledgeBase, PredFieldAccTerm) = {
    val (srcKb, src) = normalizeMutablePartsInTerm(kb, direct.exp.src)
    val (permKb, perm) = normalizeMutablePartsInTerm(srcKb, direct.perm)
    val fa = PredFieldAccTerm(
      FieldAccTerm(
        src,
        direct.exp.field,
        direct.exp.typ
      ),
      perm
    )
    (permKb, fa)
  }

  def normalizeMutablePartsInDirects(kb: KnowledgeBase, directs: Set[PredFieldAccTerm]): (KnowledgeBase, Set[PredFieldAccTerm]) = {
    directs.foldLeft((kb, Set[PredFieldAccTerm]()))((k, d) => {
      val (ukb, fa) = normalizeMutablePartsInDirect(kb, d)
      (ukb, k._2.union(Set(fa)))
    })
  }

  def normalizeMutablePartsInFold(kb: KnowledgeBase, fold: PredInstAccTerm): (KnowledgeBase, PredInstAccTerm) = {
    val (argKb, args) = normalizeMutablePartsInTermList(kb, fold.pred.args)
    val (permKb, perm) = normalizeMutablePartsInTerm(argKb, fold.perm)
    val fa = PredInstAccTerm(
      PredInst(fold.pred.name, args),
      perm
    )
    (permKb, fa)
  }

  def normalizeMutablePartsInFolded(kb: KnowledgeBase, folded: Set[PredInstAccTerm]): (KnowledgeBase, Set[PredInstAccTerm]) = {
    folded.foldLeft((kb, Set[PredInstAccTerm]()))((k, d) => {
      val (permKb, fa) = normalizeMutablePartsInFold(kb, d)
      (permKb, k._2.union(Set(fa)))
    })
  }

  def normalizeMutablePartsInTerm(kb: KnowledgeBase, term: Term): (KnowledgeBase, Term) = {
    term match {
      case AddTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, AddTerm(normA, normB))
      }
      case CondTerm(cond, left, right) => {
        val (kbC, normC) = normalizeMutablePartsInLogicTerm(kb, cond)
        val (kbA, normA) = normalizeMutablePartsInTerm(kbC, left)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, right)
        (kbB, CondTerm(normC, normA, normB))
      }
      case fa: FieldAccTerm => {
        var current: Term = fa
        var fields = Seq[String]()
        while (current.isInstanceOf[FieldAccTerm]) {
          val faa = current.asInstanceOf[FieldAccTerm]
          fields = Seq(faa.field) ++ fields
          current = faa.src
        }
        current match {
          case VarTerm(name, typ) => {
            val (assign, ref) = kb.assignment.lookup(name, typ)
            val start = kb.withAssignment(assign)
            val res = fields.foldLeft((start, ref))((acc, f) => {
              val (heap, ref) = acc._1.heap.lookupField(acc._2, f)
              (acc._1.withHeap(heap), ref)
            })

            (res._1, res._2.toVarTerm(fa.typ))
          }
          case c =>
            throw new IllegalArgumentException(s"Unable to convert field access with base ${c.getClass.getName}")
        }
      }
      case FieldPermAmountTerm(e) => {
        val (kbSrc, normSrc) = normalizeMutablePartsInTerm(kb, e.src)
        val fpa = FieldPermAmountTerm(
          FieldAccTerm(
            normSrc,
            e.field,
            e.typ
          )
        )
        (kbSrc, fpa)
      }
      case lt: IntTerm => (kb, lt)
      case term: LogicTerm => normalizeMutablePartsInLogicTerm(kb, term)
      case MulTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, MulTerm(normA, normB))
      }
      case NegTerm(t) => {
        val (kbT, normT) = normalizeMutablePartsInTerm(kb, t)
        (kbT, NegTerm(normT))
      }
      case lt: NullTerm => (kb, lt)
      case PermFracTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, PermFracTerm(normA, normB))
      }
      case SubTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, SubTerm(normA, normB))
      }
      case c => {
        throw new IllegalArgumentException(s"Unable to normalize mutable parts in term of type ${term.getClass.getCanonicalName}")
      }
    }
  }

  def normalizeMutablePartsInLogicTerm(kb: KnowledgeBase, logic: LogicTerm): (KnowledgeBase, LogicTerm) = {
    logic match {
      case AndTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInLogicTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInLogicTerm(kbA, b)
        (kbB, AndTerm(normA, normB))
      }
      case BaguetteMagic(directPrem, foldedPrem, directCons, foldedCons) => {
        val (kbA, normA) = normalizeMutablePartsInDirects(kb, directPrem)
        val (kbB, normB) = normalizeMutablePartsInFolded(kbA, foldedPrem)
        val (kbC, normC) = normalizeMutablePartsInDirects(kbB, directCons)
        val (kbD, normD) = normalizeMutablePartsInFolded(kbC, foldedCons)
        (kbD, BaguetteMagic(normA, normB, normC, normD))
      }
      case lt: BoolTerm => (kb, lt)
      case ImplTerm(prem, cons) => {
        val (kbA, normA) = normalizeMutablePartsInLogicTerm(kb, prem)
        val (kbB, normB) = normalizeMutablePartsInLogicTerm(kbA, cons)
        (kbB, ImplTerm(normA, normB))
      }
      case EqCmpTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, EqCmpTerm(normA, normB))
      }
      case GreaterCmpTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, GreaterCmpTerm(normA, normB))
      }
      case GreaterEqCmpTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, GreaterEqCmpTerm(normA, normB))
      }
      case LessCmpTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, LessCmpTerm(normA, normB))
      }
      case LessEqCmpTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, LessEqCmpTerm(normA, normB))
      }
      case NotEqCmpTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInTerm(kbA, b)
        (kbB, NotEqCmpTerm(normA, normB))
      }
      case OrTerm(a, b) => {
        val (kbA, normA) = normalizeMutablePartsInLogicTerm(kb, a)
        val (kbB, normB) = normalizeMutablePartsInLogicTerm(kbA, b)
        (kbB, OrTerm(normA, normB))
      }
      case NotTerm(t) =>{
        val (kbT, normT) = normalizeMutablePartsInLogicTerm(kb, t)
        (kbT, NotTerm(normT))
      }
      case d: PredFieldAccTerm => normalizeMutablePartsInDirect(kb, d)
      case f: PredInstAccTerm => normalizeMutablePartsInFold(kb, f)
      case VarTerm(name, typ) => {
        val (assign, ref) = kb.assignment.lookup(name, typ)
        val start = kb.withAssignment(assign)
        (start, ref.toVarTerm(typ))
      }
      case c =>
        throw new IllegalArgumentException(s"Unable to normalize mutable parts in logic term of type ${logic.getClass.getCanonicalName}")
    }
  }
}