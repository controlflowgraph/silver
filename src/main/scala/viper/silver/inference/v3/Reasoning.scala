package viper.silver.inference.v3

import viper.silver.ast.{Assert, FieldAccessPredicate, InferInfo, Inhale, LocalVarDecl, Method, PredicateAccess, PredicateAccessPredicate, Program, Ref, Seqn, Stmt, Type}
import viper.silver.inference.v3.ast.{AddTerm, AndTerm, BoolTerm, EqCmpTerm, FieldAccTerm, GreaterCmpTerm, GreaterEqCmpTerm, ImplTerm, IntTerm, LessCmpTerm, LessEqCmpTerm, LogicTerm, MulTerm, NegTerm, NotEqCmpTerm, NotTerm, NullTerm, OrTerm, PermFracTerm, PredFieldAccTerm, PredInstAccTerm, SubTerm, Term, VarTerm}
import viper.silver.inference.v3.knowledge.KnowledgeBase
import viper.silver.verifier.{Failure, Success, Verifier}

trait ProofResult {}

// represents that the current knowledge proves the statement
object Sat extends ProofResult {}

// represents that the current knowledge conflicts with the statement
object UnSat extends ProofResult {}

// represents a potential satisfaction given the current knowledge
object PotSat extends ProofResult {}

trait ReasoningEngine {
  def prove(kb: KnowledgeBase, target: LogicTerm): ProofResult
}

case class ViperReasoningEngine(verifier: Verifier, program: Program) extends ReasoningEngine {
  private def joinAll[T](sets: Seq[Set[T]]): Set[T] = {
    sets.foldLeft(Set[T]())((a, b) => a.union(b))
  }

  private def getVariablesFromTerms(terms: Seq[Term]): Set[VarTerm] = {
    joinAll(terms.map(getVariablesFromTerm))
  }

  private def getVariablesFromTerm(term: Term): Set[VarTerm] = {
    term match {
      case AddTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case FieldAccTerm(src, field, typ) => getVariablesFromTerm(src)
      case IntTerm(value) => Set()
      case AndTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case BoolTerm(value) => Set()
      case EqCmpTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case GreaterCmpTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case GreaterEqCmpTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case ImplTerm(prem, cons) => getVariablesFromTerms(Seq(prem, cons))
      case LessCmpTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case LessEqCmpTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case NotEqCmpTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case NotTerm(t) => getVariablesFromTerm(t)
      case OrTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case PredFieldAccTerm(exp, perm) => getVariablesFromTerms(Seq(exp, perm))
      case PredInstAccTerm(pred, perm) => getVariablesFromTerms(pred.args ++ Seq(perm))
      case v: VarTerm => Set(v)
      case MulTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case NegTerm(t) => getVariablesFromTerm(t)
      case NullTerm() => Set()
      case PermFracTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case SubTerm(a, b) => getVariablesFromTerms(Seq(a, b))
      case t => {
        throw new IllegalArgumentException(s"Unable to extract variables from term of type ${t.getClass.getCanonicalName}")
      }
    }
  }

  private def getVariablesOfKnowledgeBase(fieldTypes: Map[String, Type], kb: KnowledgeBase): Set[VarTerm] = {
    val fromAssignment = kb.assignment.variables.map(v => VarTerm(v._1, v._2._2)).toSet
    val fromAssignmentValRefs = kb.assignment.variables.map(v => v._2._1.toVarTerm(v._2._2)).toSet
    // TODO: is this a safe mapping or could it contain variables that are actually primitive?
    val fromHeap = kb.heap.objMap.map(v => v._1.toVarTerm(Ref)).toSet
    val fromHeapFields = kb.heap.objMap.flatMap(v => {
      v._2.fields.map(f => {
        val typ = fieldTypes(f._1)
        f._2.toVarTerm(typ)
      })
    }).toSet
    val fromDirect = kb.direct.permissions.map(a => getVariablesFromTerms(Seq(a._1, a._2)))
    val fromFolded = kb.folded.permissions.map(f => getVariablesFromTerms(f._1.args ++ Seq(f._2)))
    val fromPartial = getVariablesFromTerms(kb.partial.partial.toSeq)
    val fromInfo = getVariablesFromTerm(kb.info)

    val combined = Seq(fromAssignment, fromAssignmentValRefs, fromHeap, fromHeapFields, fromPartial, fromInfo) ++ fromDirect ++ fromFolded
    joinAll(combined)
  }

  def prove(kb: KnowledgeBase, target: LogicTerm): ProofResult = {
    val resNormal = proveDirect(kb, target)
    resNormal match {
      case Sat => Sat
      case UnSat => {
        val resNegated = proveDirect(kb, NotTerm(target))
        resNegated match {
          case Sat => UnSat
          case UnSat => PotSat
        }
      }
    }
  }

  def proveDirect(kb: KnowledgeBase, target: LogicTerm): ProofResult = {
    // get the variables used in all kinds of terms in the knowledge base
    val usedVars = getVariablesOfKnowledgeBase(kb.fieldTypes, kb)
    val decls = usedVars.map(e => LocalVarDecl(e.name, e.typ)()).toSeq

    // inhale the pure information
    val infoInhales = Inhale(kb.info.toExp())()


    // inhale the available field permissions
    val directInhales: Seq[Stmt] = kb.direct.permissions.map(e => {
      val faccExp = e._1.toExp()
      val permExp = e._2.toExp()
      Inhale(FieldAccessPredicate(faccExp, Some(permExp))())()
    }).toSeq

    // inhale the available predicate permissions
    val foldedInhales: Seq[Stmt] = kb.folded.permissions.map(e => {
      val predAcc = PredicateAccess(
        e._1.args.map(e => e.toExp()),
        e._1.name
      )()
      val permExp = e._2.toExp()
      Inhale(PredicateAccessPredicate(predAcc, Some(permExp))())()
    }).toSeq

    // inhale partial/potential permissions
    // (maybe useless since these are parts which are unproven)
    val partialInhales = kb.partial.partial.map(i => {
      Inhale(i.toExp())()
    }).toSeq

    // generate equivalence information within the assignment
    val equivInfoFromAssignment = kb.assignment.variables.map(v => {
        val typ = v._2._2
        val variable = VarTerm(v._1, typ)
        val value = v._2._1.toVarTerm(typ)
        EqCmpTerm(variable, value)
      })
      .map(v => v.toExp())
      .map(v => Inhale(v)())

    // generate equivalence information within the heap
    val equivInfoFromHeap = kb.heap.objMap.flatMap(v => {
        val obj = v._1.toVarTerm(Ref)
        v._2.fields.map(f => {
          val typ = kb.fieldTypes(f._1)
          val field = FieldAccTerm(obj, f._1, typ)
          val res = f._2.toVarTerm(typ)
          EqCmpTerm(field, res)
        })
      })
      .map(v => v.toExp())
      .map(v => Inhale(v)())


    // assertion for the term that needs to be proven
    val targetAssertion = Assert(target.toExp())()

    // generate abstract methods
    // (might be useless since no method calls are present generated inhale/assert statements)
    val methodStubs = program.methods.map(m => Method(
      m.name,
      m.formalArgs,
      m.formalReturns,
      m.pres,
      m.posts,
      None
    )())

    // combine all statements into a method and join into a method
    // with the contextual information about the fields etc
    val stmts: Seq[Stmt] = Seq(infoInhales) ++ directInhales ++ foldedInhales ++ partialInhales ++ equivInfoFromAssignment ++ equivInfoFromHeap ++ Seq(targetAssertion)

    val body = Seqn(
      stmts,
      decls
    )()

    val proofMethod = Method("proof", Seq(), Seq(), Seq(), Seq(), Some(body))()

    val methods = methodStubs ++ Seq(proofMethod)

    val proofProgram = Program(
      this.program.domains,
      this.program.fields,
      this.program.functions,
      this.program.predicates,
      methods,
      this.program.extensions,
      new InferInfo()
    )()

    val result = this.verifier.verify(proofProgram)

    println(s"VERIFICATION RESULT: ${result}")

    result match {
      case Success => Sat
      case Failure(errors) => UnSat
    }
  }
}

