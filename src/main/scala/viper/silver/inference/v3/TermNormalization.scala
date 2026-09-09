package viper.silver.inference.v3

import viper.silver.ast.Type
import viper.silver.inference.v3.ast.{AddTerm, AndTerm, BoolTerm, EqCmpTerm, FieldAccTerm, GreaterCmpTerm, GreaterEqCmpTerm, IntTerm, LessCmpTerm, LessEqCmpTerm, LogicTerm, MulTerm, NegTerm, NotEqCmpTerm, NotTerm, NullTerm, OrTerm, PermFracTerm, SubTerm, Term, VarTerm}
import viper.silver.inference.v3.knowledge.KnowledgeBase

object TermNormalization {

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
}