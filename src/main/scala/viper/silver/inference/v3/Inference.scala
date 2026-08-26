package viper.silver.inference.v3

import viper.silver.ast.{
  AbstractAssign, AbstractDomainFuncApp, AbstractLocalVar, AccessPredicate, AnySetBinExp, AnySetExp, AnySetUnExp, Apply, Applying, Assert, Asserting, Assume, BackendFuncApp, BinExp, CondExp, DebugLabelledOld, DomainBinExp, DomainFuncApp, DomainOpExp, DomainUnExp, EmptyMap, EmptyMultiset, EmptySeq, EmptySet, EqualityCmp, Exhale, Exists, Exp, ExplicitMap, ExplicitMultiset, ExplicitSeq, ExplicitSet, ExtensionStmt, FieldAccess, FieldAccessPredicate, FieldAssign, Fold, ForPerm, Forall, FuncApp, FuncLikeApp, Function, Goto, If, Inhale, InhaleExhaleExp, Injection, Label, LabelledOld, Let, Literal, LocalVar, LocalVarAssign, LocalVarDecl, LocalVarDeclStmt, LocalVarWithVersion, LocationAccess, MagicWand, MapCardinality, MapContains, MapDomain, MapExp, MapLookup, MapRange, MapUpdate, Maplet, Method, MethodCall, MultisetExp, NewStmt, Old, OldExp, Package, PermExp, PredicateAccess, PredicateAccessPredicate, Program, QuantifiedExp, Quasihavoc, Quasihavocall, RangeSeq, Ref, Result, SeqAppend, SeqContains, SeqDrop, SeqExp, SeqIndex, SeqLength, SeqTake, SeqUpdate, Seqn, SetExp, Stmt, UnExp, Unfold, Unfolding, While
}
import viper.silver.inference.v3.ast._

import scala.annotation.tailrec
import scala.collection.mutable

object DependencyAnalysis {
  private def computeDependencyGraph(reps: Map[String, InternalMethod]): Map[String, Set[String]] = {
    reps.map(m => m._1 -> m._2.rep.lines.values.flatMap {
      case CallLine(_, _, method, _, _) => Some(method)
      case _ => None
    }.toSet)
  }

  private def computeTopologicalOrder(open: Set[String], deps: Map[String, Set[String]]): Seq[Set[String]] = {
    if (open.isEmpty) {
      Seq()
    }
    else {
      // TODO: how to fix mutually recursive methods?
      val done = open.filter(o => deps(o).intersect(open).diff(Set(o)).isEmpty)
      if (done.isEmpty) {
        throw new IllegalStateException("Mutually recursive functions not in topological ordering supported!")
      }
      Seq(done) ++ computeTopologicalOrder(open.diff(done), deps)
    }
  }

  def computeTopologicalOrder(reps: Map[String, InternalMethod]): Seq[Set[String]] = {
    val deps = computeDependencyGraph(reps)
    computeTopologicalOrder(deps.keySet, deps)
  }

  def computeFlatTopologicalOrder(reps: Map[String, InternalMethod]): Seq[String] = {
    computeTopologicalOrder(reps).flatMap(_.toSeq)
  }
}

object MutationAnalysis {
  def computeDirectMutation(reps: Map[String, InternalMethod]): Map[String, Boolean] = {
    reps.map(m => m._1 -> m._2.rep.lines.values.exists {
      case _: FieldAssignLine => true
      case _ => false
    })
  }

  def computeIndirectMutation(deps: Map[String, Set[String]], mutation: Map[String, Boolean]): Map[String, Boolean] = {
    FixedPoint.compute(mutation, (m: Map[String, Boolean]) => m.map(e => e._1 -> (e._2 || deps(e._1).exists(m))))
  }
}

object FunctionDerivation {

  private def containsRecursiveFunctionCall(exp: Exp, func: Set[String]): Boolean = {
    // TODO: fix mutually recursive functions
    exp match {
      case predicate: AccessPredicate => predicate match {
        case MagicWand(left, right) => containsRecursiveFunctionCall(left, func) || containsRecursiveFunctionCall(right, func)
        case FieldAccessPredicate(loc, permExp) => containsRecursiveFunctionCall(loc, func) || permExp.exists(p => containsRecursiveFunctionCall(p, func))
        case PredicateAccessPredicate(loc, permExp) => containsRecursiveFunctionCall(loc, func) || permExp.exists(p => containsRecursiveFunctionCall(p, func))
      }
      case InhaleExhaleExp(in, ex) => containsRecursiveFunctionCall(in, func) || containsRecursiveFunctionCall(ex, func)
      case exp: PermExp => false // TODO: fix if perm exp could have rec func call
      case access: LocationAccess => access match {
        case FieldAccess(rcv, field) => containsRecursiveFunctionCall(rcv, func)
        case PredicateAccess(args, predicateName) => args.exists(a => containsRecursiveFunctionCall(a, func))
      }
      case CondExp(cond, thn, els) => containsRecursiveFunctionCall(cond, func) || containsRecursiveFunctionCall(thn, func) || containsRecursiveFunctionCall(els, func)
      case Unfolding(acc, body) => containsRecursiveFunctionCall(body, func)
      case Applying(wand, body) => containsRecursiveFunctionCall(body, func)
      case Asserting(a, body) => containsRecursiveFunctionCall(body, func)
      case Let(variable, exp, body) => containsRecursiveFunctionCall(exp, func) || containsRecursiveFunctionCall(body, func)
      case exp: QuantifiedExp => exp match {
        case Forall(variables, triggers, exp) => containsRecursiveFunctionCall(exp, func)
        case Exists(variables, triggers, exp) => containsRecursiveFunctionCall(exp, func)
        case ForPerm(variables, resource, body) => containsRecursiveFunctionCall(body, func)
      }
      case ForPerm(variables, resource, body) => containsRecursiveFunctionCall(body, func)
      case localVar: AbstractLocalVar => localVar match {
        case LocalVar(name, typ) => false
        case Result(typ) => false
        case LocalVarWithVersion(name, typ) => false
      }
      case exp: SeqExp => exp match {
        case EmptySeq(elemTyp) => false
        case ExplicitSeq(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
        case RangeSeq(low, high) => containsRecursiveFunctionCall(low, func) || containsRecursiveFunctionCall(high, func)
        case SeqAppend(left, right) => containsRecursiveFunctionCall(left, func) || containsRecursiveFunctionCall(right, func)
        case SeqIndex(s, idx) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(idx, func)
        case SeqTake(s, n) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(n, func)
        case SeqDrop(s, n) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(n, func)
        case SeqContains(elem, s) => containsRecursiveFunctionCall(elem, func) || containsRecursiveFunctionCall(s, func)
        case SeqUpdate(s, idx, elem) => containsRecursiveFunctionCall(s, func) || containsRecursiveFunctionCall(idx, func) || containsRecursiveFunctionCall(elem, func)
        case SeqLength(s) => containsRecursiveFunctionCall(s, func)
      }
      case exp: SetExp => exp match {
        case exp: AnySetExp => exp match {
          case exp: AnySetUnExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case exp: AnySetBinExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case MapDomain(base) => containsRecursiveFunctionCall(base, func)
          case MapRange(base) => containsRecursiveFunctionCall(base, func)
        }
        case EmptySet(elemTyp) => false
        case ExplicitSet(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
      }
      case exp: MultisetExp => exp match {
        case exp: AnySetExp => exp match {
          case exp: AnySetUnExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case exp: AnySetBinExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case MapDomain(base) => containsRecursiveFunctionCall(base, func)
          case MapRange(base) => containsRecursiveFunctionCall(base, func)
        }
        case EmptyMultiset(elemTyp) => false
        case ExplicitMultiset(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
      }
      case exp: MapExp => exp match {
        case EmptyMap(keyType, valueType) => false
        case ExplicitMap(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
        case Maplet(key, value) => containsRecursiveFunctionCall(key, func) || containsRecursiveFunctionCall(value, func)
        case MapUpdate(base, key, value) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func) || containsRecursiveFunctionCall(value, func)
        case MapLookup(base, key) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func)
        case MapContains(key, base) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func)
        case MapCardinality(base) => containsRecursiveFunctionCall(base, func)
      }
      case literal: Literal => false
      case DomainFuncApp(funcname, args, typVarMap) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
      case app: FuncLikeApp => app match {
        case FuncApp(funcname, args) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
        case app: AbstractDomainFuncApp => app match {
          case DomainFuncApp(funcname, args, typVarMap) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
          case BackendFuncApp(backendFuncName, args) => func.contains(backendFuncName) || args.exists(a => containsRecursiveFunctionCall(a, func))
          case exp: DomainOpExp => exp match {
            case exp: DomainBinExp => containsRecursiveFunctionCall(exp.left, func) || containsRecursiveFunctionCall(exp.right, func)
            case exp: DomainUnExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          }
        }
      }
      case exp: BinExp => exp match {
        case exp: AnySetBinExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
        case cmp: EqualityCmp => cmp.args.exists(a => containsRecursiveFunctionCall(a, func))
      }
      case exp: UnExp => exp match {
        case exp: OldExp => exp match {
          case Old(exp) => containsRecursiveFunctionCall(exp, func)
          case LabelledOld(exp, oldLabel) => containsRecursiveFunctionCall(exp, func)
          case DebugLabelledOld(exp, oldLabel) => containsRecursiveFunctionCall(exp, func)
        }
      }
    }
  }

  def computeFunctionBaseCases(exp: Exp, func: Set[String]): Set[Exp] = {
    if (!containsRecursiveFunctionCall(exp, func))
      Set(exp)
    else
      exp match {
        case access: LocationAccess => access match {
          case FieldAccess(rcv, field) => Set(exp)
          case _ => Set()
        }
          //        case access: ResourceAccess =>
        case CondExp(cond, thn, els) =>
          if (containsRecursiveFunctionCall(cond, func)) Set()
          else computeFunctionBaseCases(thn, func).union(computeFunctionBaseCases(els, func))
        case Let(variable, exp, body) =>
          if (containsRecursiveFunctionCall(exp, func)) Set()
          else computeFunctionBaseCases(body, func)
          //        case exp: QuantifiedExp =>
          //        case ForPerm(variables, resource, body) =>
        case localVar: AbstractLocalVar => Set()
        case exp: SeqExp => Set()
        case exp: SetExp => Set()
        case exp: MultisetExp => Set()
        case exp: MapExp => Set()
        case literal: Literal => Set()
          //        case trigger: PossibleTrigger =>
          //        case trigger: ForbiddenInTrigger =>
        case FuncApp(funcname, args) => Set()
        case exp: BinExp => Set() // TODO: maybe refine this if there is a use for different base cases
        case exp: UnExp => Set() // TODO: maybe refine this if there is a use for different base cases
          //        case lhs: Lhs =>
          //        case exp: ExtensionExp =>
      }
  }


  private def computeExprRep(stmt: Stmt, resultVariable: String, recursive: String): Option[Exp] = {
    stmt match {
      case NewStmt(lhs, fields) => None
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) =>
          if (lhs.name.equals(resultVariable))
            Some(rhs)
          else None
        case FieldAssign(lhs, rhs) => None
      }
      case c@MethodCall(methodName, args, targets) =>
        if (methodName.equals(recursive))
          Some(FuncApp("Func$" + recursive, args)(c.pos, c.info, targets.head.typ, c.errT))
        else None
      case Exhale(exp) => None
      case Inhale(exp) => None
      case Assert(exp) => None
      case Assume(exp) => None
        // TODO: maybe this part can be ignored instead of producing none result when doing the functionalization
      case Fold(acc) => None
      case Unfold(acc) => None
      case Package(wand, proofScript) => None
      case Apply(exp) => None
      case Seqn(ss, scopedSeqnDeclarations) => {
        if (ss.isEmpty) {
          None
        }
        else if (ss.length == 1) {
          computeExprRep(ss.last, resultVariable, recursive)
        }
        else {
          // last statement in the sequence must be convertible
          // all previous statements are assumed to be local assignments
          // they are translated to let bindings
          val prev = ss.dropRight(1)
          val last: Option[Exp] = computeExprRep(prev.last, resultVariable, recursive)
          prev.foldRight(last)((stmt, result) => result.flatMap(
            m => {
              stmt match {
                case l@LocalVarAssign(lhs, rhs) => {
                  Some(Let(LocalVarDecl(lhs.name, lhs.typ)(lhs.pos, lhs.info, lhs.errT),
                    rhs,
                    m
                  )(l.pos, l.info, l.errT))
                }
                  // case Seqn(ss, scopedSeqnDeclarations) => TODO: allow nesting of sequences although this might not be relevant
                  // case If(cond, thn, els) => TODO: potentially allow this if there is a usecase / valid mapping
                case _ => None
              }
            }
          ))
        }
      }
      case i@If(cond, thn, els) => {
        val expA = computeExprRep(thn, resultVariable, recursive)
        val expB = computeExprRep(els, resultVariable, recursive)
        (expA, expB) match {
          case (Some(a), Some(b)) => Some(CondExp(cond, a, b)(i.pos, i.info, i.errT))
          case _ => None
        }
      }
      case Injection(id) => None
      case While(cond, invs, body) => None
      case Label(name, invs) => None
      case Goto(target) => None
      case LocalVarDeclStmt(decl) => None // TODO: check if this comes up and needs to be handled gracefully
      case Quasihavoc(lhs, exp) => None
      case Quasihavocall(vars, lhs, exp) => None
      case stmt: ExtensionStmt => None
    }
  }

  def computeFunctionalRepresentation(method: Method): Option[Function] = {
    // FIND THE FUNCTIONS THAT RETURN A REF from a field
    //    compute an additional function that returns the amount of permission from that field (if it exists)
    //    ---> then generate the appropriate function
    // THE FUNCTIONS THAT RETURN PRIMITIVE VALUES ARE IRRELEVANT SINCE THEIR VALUE CAN BE COPIED AND HAS NO ACCESS PERMISSIONS

    if (method.formalReturns.length == 1 && method.formalReturns.head.typ.equals(Ref)) {
      val firstReturn = method.formalReturns.head
      val bodyExp = method.body.flatMap(b => computeExprRep(b, firstReturn.name, method.name))
      // in the posts the resulting formal return needs to be replaced with result
      bodyExp.map(b => Function(
        "Func$" + method.name, method.formalArgs,
        firstReturn.typ, method.pres,
        method.posts, Some(b))
      (method.pos, method.info, method.errT))
    }
    else {
      println(s"Method ${method.name} does not have exactly 1 return!")
      None
    }
  }
}

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

case class ValRef(id: Int) {
  def pretty(): String = {
    s"ref::${this.id}"
  }
}

case class Assignment(rc: RefCounter, variables: Map[String, ValRef]) {
  def this(rc: RefCounter) = {
    this(rc, Map())
  }

  def assign(name: String, ref: ValRef): Assignment = {
    Assignment(this.rc, this.variables.updated(name, ref))
  }

  def pretty(): String = {
    this.variables.map(e => s"${e._1}: ${e._2.pretty()}").mkString("\n")
  }

  def lookup(name: String): (Assignment, ValRef) = {
    if (this.variables.contains(name)) {
      (this, this.variables(name))
    }
    else {
      val fresh = this.rc.freshValRef()
      (Assignment(this.rc, this.variables.updated(name, fresh)), fresh)
    }
  }
}


case class RefCounter(counter: Counter) {
  def freshValRef(): ValRef = {
    ValRef(this.counter.next())
  }
}

case class Obj(ref: ValRef, fields: Map[String, ValRef]) {
  def assign(field: String, ref: ValRef): Obj = {
    Obj(this.ref, this.fields.updated(field, ref))
  }
}

case class Heap(rc: RefCounter, objMap: Map[ValRef, Obj]) {

  def this(rc: RefCounter) = {
    this(rc, Map())
  }

  def lookup(ref: ValRef): (Heap, Obj) = {
    if (this.objMap.contains(ref)) {
      (this, this.objMap(ref))
    }
    else {
      val fresh = Obj(ref, Map())
      (Heap(this.rc, this.objMap.updated(ref, fresh)), fresh)
    }
  }

  def pretty(): String = {
    this.objMap.values.map(o => s"${o.ref.pretty()}:\n${o.fields.map(e => s"${e._1}: ${e._2.pretty()}").mkString("\n").indent(2)}".indent(2)).mkString("\n")
  }

  def lookupField(r: ValRef, field: String): (Heap, ValRef) = {
    val (h, o) = lookup(r)
    if (o.fields.contains(field)) {
      (h, o.fields(field))
    }
    else {
      val fresh = this.rc.freshValRef()
      val uo = o.assign(field, fresh)
      (Heap(this.rc, this.objMap.updated(r, uo)), fresh)
    }
  }

  def assignField(r: ValRef, field: String, v: ValRef): Heap = {
    Heap(this.rc, this.objMap.updated(r, this.objMap(r).assign(field, v)))
  }
}

case class Frac(n: Int, d: Int) {

  @tailrec
  private def gcd(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a % b)

  private val common = gcd(n.abs, d.abs)

  val numerator: Int = this.n / common
  val denominator: Int = this.d / common

  def +(that: Frac): Frac =
    Frac(
      numerator * that.denominator + that.numerator * denominator,
      denominator * that.denominator
    )

  def *(that: Frac): Frac =
    Frac(numerator * that.numerator, denominator * that.denominator)
}

case class DirectPermissionMask(permissions: Map[FieldAccTerm, Term]) {
  def this() = {
    this(Map())
  }

  def inhale(b: PredFieldAccTerm): DirectPermissionMask = {
    val before = this.permissions.getOrElse(b.exp, PermFracTerm(IntTerm(0), IntTerm(1)))
    val beforeSimp = AddTerm(before, b.perm)
    val afterSimp = TermRewriter.simplify(beforeSimp)
    DirectPermissionMask(
      this.permissions.updated(b.exp, afterSimp)
    )
  }

  def pretty(): String = {
    this.permissions.map(e => s"${e._1.pretty()}: ${e._2.pretty()}").mkString("\n")
  }

  def getAmount(pred: FieldAccTerm): Term = {
    this.permissions.getOrElse(pred, PermFracTerm(IntTerm(0), IntTerm(1)))
  }

  def substitute(ts: TermSub): DirectPermissionMask = {
    DirectPermissionMask(
      this.permissions.map(e => (
        FieldAccTerm(e._1.src.substitute(ts), e._1.field, e._1.typ),
        e._2.substitute(ts))
      )
    )
  }

  def exhale(b: PredFieldAccTerm): DirectPermissionMask = {
    val before = this.permissions.getOrElse(b.exp, PermFracTerm(IntTerm(0), IntTerm(1)))
    val beforeSimp = SubTerm(before, b.perm)
    val afterSimp = TermRewriter.simplify(beforeSimp)
    DirectPermissionMask(
      this.permissions.updated(b.exp, afterSimp)
    )
  }
}

case class FoldedPermissionMask(permissions: Map[PredInst, Term]) {
  def this() = {
    this(Map())
  }

  def inhale(b: PredInstAccTerm): FoldedPermissionMask = {
    val current = this.permissions.getOrElse(b.pred, PermFracTerm(IntTerm(0), IntTerm(1)))
    val amount = TermRewriter.simplify(AddTerm(current, b.perm))
    FoldedPermissionMask(
      this.permissions.updated(b.pred, amount)
    )
  }

  def pretty(): String = {
    this.permissions.map(e => s"${e._1.pretty()}: ${e._2.pretty()}").mkString("\n")
  }

  def exhale(pa: PredInstAccTerm): FoldedPermissionMask = {
    exhale(pa.pred, pa.perm)
  }

  def exhale(pred: PredInst, perm: Term): FoldedPermissionMask = {
    val current = this.permissions.getOrElse(pred, PermFracTerm(IntTerm(0), IntTerm(1)))
    val amount = TermRewriter.simplify(SubTerm(current, perm))
    FoldedPermissionMask(
      this.permissions.updated(pred, amount)
    )
  }

  def substitute(ts: TermSub): FoldedPermissionMask = {
    FoldedPermissionMask(
      this.permissions.map(e => (
        PredInst(e._1.name, e._1.args.map(a => a.substitute(ts))),
        e._2.substitute(ts)
      ))
    )
  }

  def getAmount(pred: PredInst): Term = {
    this.permissions.getOrElse(pred, PermFracTerm(IntTerm(0), IntTerm(1)))
  }
}

case class DNF(clauses: Set[Set[Comparison]]) {

  def and(other: DNF): DNF = {
    DNF(this.clauses.toSeq.flatMap(p => other.clauses.toSeq.map(q => q.union(p))).toSet)
  }

  def prune(): DNF = {
    DNF(this.clauses.filter(d => !this.clauses.exists(v => v.subsetOf(d) && !v.equals(d))))
  }

  def negate(): DNF = {
    val sub = this.clauses.map(v => v.map(c => c.negate()))
    val res = sub.foldLeft(Set(Set[Comparison]()))((acc, neg) => {
      neg.toSeq.flatMap(e => acc.map(a => a.union(Set(e)))).toSet
    })
    DNF(res)
  }

  def or(other: DNF): DNF = {
    DNF(this.clauses.union(other.clauses))
  }

  def pretty(): String = {
    this.clauses.map(v => v.map(a => a.pretty()).mkString(" & ")).mkString(" OR \n")
  }

  def substitute(ts: TermSub): DNF = {
    DNF(this.clauses.map(c => c.map(i => i.subst(ts))))
  }

  def toLogicTerm(): LogicTerm = {
    this.clauses.map(
        c => c.map(_.toLogicTerm())
          .reduceLeftOption(AndTerm)
          .getOrElse(BoolTerm(true))
      )
      .reduceLeftOption(OrTerm)
      .getOrElse(BoolTerm(false))
  }
}

trait ProofResult {}

// represents that the current knowledge proves the statement
object Sat extends ProofResult {}

// represents that the current knowledge conflicts with the statement
object UnSat extends ProofResult {}

// represents a potential satisfaction given the current knowledge
object PotSat extends ProofResult {}

case class Potential(partial: Set[ImplTerm]) {

  def this() = {
    this(Set())
  }

  def substitute(ts: TermSub): Potential = {
    Potential(this.partial.map(i => ImplTerm(
      i.prem.substitute(ts).asInstanceOf[LogicTerm],
      i.cons.substitute(ts).asInstanceOf[LogicTerm]
    )))
  }

  def pretty(): String = {
    this.partial.map(i => i.pretty()).toSeq.mkString("\n")
  }

  def inhale(partial: Seq[ImplTerm]): Potential = {
    // TODO: this merge can lose information when having two implications of the same form
    //       e.g. a ==> acc(A, 1/2) && b ==> a ==> acc(A, 1/2)
    //       with inhale b this would lead to merging
    //       a ==> acc(A, 1/2) && a ==> acc(A, 1/2)
    //      into just:   { a ==> acc(A, 1/2) }
    Potential(this.partial.union(partial.toSet))
  }
}

case class KnowledgeBase(assignment: Assignment, heap: Heap, direct: DirectPermissionMask, folded: FoldedPermissionMask, info: DNF, partial: Potential) {

  def prove(term: LogicTerm): Boolean = {
    proveDetailed(term) == Sat
  }

  private def resultOfBool(value: Boolean): ProofResult = {
    if (value) Sat
    else UnSat
  }

  def proveClause(cls: Set[Comparison], term: LogicTerm): ProofResult = {
    term match {
      case AndTerm(a, b) => {
        val resA = proveClause(cls, a)
        val resB = proveClause(cls, b)
        mergeProofResultsConj(resA, resB)
      }
      case BoolTerm(value) => resultOfBool(value)
      case c: Comparison => {
        val isSat = cls.contains(c)
        val isUn = cls.contains(c.negate())
        if (isSat) Sat
        else if (isUn) UnSat
        else PotSat
      }
      case ImplTerm(prem, cons) => proveClause(cls, OrTerm(NotTerm(prem), cons))
      case NotTerm(t) => {
        val resT = proveClause(cls, t)
        resT match {
          case PotSat => PotSat
          case Sat => UnSat
          case UnSat => Sat
          case _ => {
            throw new IllegalArgumentException(s"Unable to negate proof result ${resT}")
          }
        }
      }
      case OrTerm(a, b) => {
        val resA = proveClause(cls, a)
        val resB = proveClause(cls, b)
        mergeProofResultsDis(resA, resB)
      }
      case _ => {
        throw new IllegalArgumentException(s"Unable to process term of type ${term.getClass.getCanonicalName} while proving")
      }
    }
  }

  private def mergeProofResultsDis(a: ProofResult, b: ProofResult): ProofResult = {
    (a, b) match {
      case (Sat, Sat) => Sat
      case (Sat, UnSat) => Sat
      case (UnSat, Sat) => Sat
      case (UnSat, UnSat) => UnSat
      case (Sat, PotSat) => Sat
      case (PotSat, Sat) => Sat
      case (PotSat, UnSat) => PotSat
      case (UnSat, PotSat) => PotSat
      case _ => {
        throw new IllegalArgumentException(s"Unknown combination of proof results ${a} & ${b}")
      }
    }
  }

  private def mergeProofResultsConj(a: ProofResult, b: ProofResult): ProofResult = {
    (a, b) match {
      case (Sat, Sat) => Sat
      case (Sat, UnSat) => UnSat
      case (UnSat, Sat) => UnSat
      case (UnSat, UnSat) => UnSat
      case (Sat, PotSat) => PotSat
      case (PotSat, Sat) => PotSat
      case (PotSat, UnSat) => UnSat
      case (UnSat, PotSat) => UnSat
      case _ => {
        throw new IllegalArgumentException(s"Unknown combination of proof results ${a} & ${b}")
      }
    }
  }

  def proveDetailed(term: LogicTerm): ProofResult = {
    this.info.clauses.map(c => proveClause(c, term))
      .foldLeft(Sat.asInstanceOf[ProofResult])(mergeProofResultsConj)
  }

  def update(fun: Assignment => Heap => DirectPermissionMask => FoldedPermissionMask => DNF => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, DNF)): KnowledgeBase = {
    update((a, h, d, f, i, p) => {
      val res = fun(a)(h)(d)(f)(i)
      (res._1, res._2, res._3, res._4, res._5, p)
    })
  }

  def update(f: (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, DNF, Potential) => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, DNF, Potential)): KnowledgeBase = {
    val res = f(this.assignment, this.heap, this.direct, this.folded, this.info, this.partial)
    KnowledgeBase(res._1, res._2, res._3, res._4, res._5, res._6)
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

  def hasEnoughPermissions(amount: Term, higher: Term): Boolean = {
    val lowSimp = TermRewriter.simplify(amount)
    val highSimp = TermRewriter.simplify(higher)
    (lowSimp, highSimp) match {
      case (PermFracTerm(IntTerm(a), IntTerm(b)), PermFracTerm(IntTerm(c), IntTerm(d))) => {
        val fracA = a.doubleValue / b.doubleValue
        val fracB = c.doubleValue / d.doubleValue
        fracA <= fracB
      }
      case _ => false
    }
  }

  // TODO: add max search depth to the re/unfolding search
  private def searchDepth: Int = 10

  def findUnfoldingStrategyInPredicate(defs: Map[String, PredDef], fa: PredInstAccTerm, instance: PredInstAccTerm): Option[RefoldingStep] = {
    val predDef = defs(instance.pred.name)
    val instantiated = predDef.instantiate(instance.pred)
    // TODO: EXTEND THE KNOWLEDGE WITH THE PURE INFORMATION WHEN UNFOLDING
    val pure = PredicateCollector.stripToPure(instantiated, this)

    val direct = PredicateCollector.collectDirectPredicates(instantiated, this)
    val folded = PredicateCollector.collectFoldedPredicates(instantiated, this)
    val subs = folded.flatMap(v => findUnfoldingStrategyInPredicate(defs, fa, v))

    val containedOnDirectLevel = folded.exists(v => v.pred.equals(fa.pred))
    val containedOnSubLevel = subs.nonEmpty

    if (containedOnDirectLevel || containedOnSubLevel) {
      Some(UnfoldingStep(instance.pred, instance.perm, subs))
    }
    else {
      None
    }
  }


  def findUnfoldingStrategyInPredicate(defs: Map[String, PredDef], fa: PredFieldAccTerm, instance: PredInstAccTerm): Option[RefoldingStep] = {
    val predDef = defs(instance.pred.name)
    val instantiated = predDef.instantiate(instance.pred)
    // TODO: EXTEND THE KNOWLEDGE WITH THE PURE INFORMATION WHEN UNFOLDING
    val pure = PredicateCollector.stripToPure(instantiated, this)

    val direct = PredicateCollector.collectDirectPredicates(instantiated, this)
    val folded = PredicateCollector.collectFoldedPredicates(instantiated, this)
    val subs = folded.flatMap(v => findUnfoldingStrategyInPredicate(defs, fa, v))

    val containedOnDirectLevel = direct.exists(v => v.exp.equals(fa.exp))
    val containedOnSubLevel = subs.nonEmpty

    if (containedOnDirectLevel || containedOnSubLevel) {
      Some(UnfoldingStep(instance.pred, instance.perm, subs))
    }
    else {
      None
    }
  }

  private def isClearlyZeroPerm(t: Term): Boolean = {
    TermRewriter.simplify(t) match {
      case PermFracTerm(IntTerm(a), _) => a.equals(BigInt.int2bigInt(0))
      case _ => true
    }
  }

  def findUnfoldingStrategy(defs: Map[String, PredDef], fa: PredInstAccTerm): Option[RefoldingStrategy] = {
    // TODO: check if it is even possible that the permission amount is reachable
    val directAmount = this.folded.getAmount(fa.pred)
    if (hasEnoughPermissions(fa.perm, directAmount)) {
      Some(RefoldingStrategy(Seq()))
    }
    else {
      val mapped: Seq[PredInstAccTerm] = this.folded.permissions.map(e => PredInstAccTerm(e._1, e._2))
        .filter(i => !isClearlyZeroPerm(i.perm))
        .toSeq

      val strats = mapped.flatMap(v => findUnfoldingStrategyInPredicate(defs, fa, v))
      Some(RefoldingStrategy(strats))
    }
  }


  def findUnfoldingStrategy(defs: Map[String, PredDef], fa: PredFieldAccTerm): Option[RefoldingStrategy] = {
    // TODO: check if it is even possible that the permission amount is reachable
    val directAmount = this.direct.getAmount(fa.exp)
    if (hasEnoughPermissions(fa.perm, directAmount)) {
      Some(RefoldingStrategy(Seq()))
    }
    else {
      val mapped: Seq[PredInstAccTerm] = this.folded.permissions.map(e => PredInstAccTerm(e._1, e._2))
        .filter(i => !isClearlyZeroPerm(i.perm))
        .toSeq

      val strats = mapped.flatMap(v => findUnfoldingStrategyInPredicate(defs, fa, v))
      Some(RefoldingStrategy(strats))

      //      val res = findContainedFieldPermission(defs, mapped, fa.pred, 0)
      //      println(s"found ${res.length} refolding strategies for ${fa.pretty()}")
      //      res.map(e => RefoldingStrategy(e.steps, TermRewriter.simplify(e.perm)))
      //        .foreach(e => println(e.pretty()))
      //      //        res.flatMap(p => findContainedFieldPermission(defs, p., fa.pred))
      //      //        .foreach(a => println(s"found unfolding strategy: ${fa.pred.pretty()} ${a._1.pretty()}: ${a._2.pretty()}"))
      //      None
    }
  }

  def unfold(defs: Map[String, PredDef], pred: PredInst, perm: Term): KnowledgeBase = {
    update(a => h => d => f => i => {
      val predDef = defs(pred.name)

      val instantiated = predDef.instantiate(pred)
      val direct = PredicateCollector.collectDirectPredicates(instantiated, this)
      val folded = PredicateCollector.collectFoldedPredicates(instantiated, this)
      val pure = PredicateCollector.stripToPure(instantiated, this)

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

  def fold(defs: Map[String, PredDef], pred: PredInst, perm: Term): KnowledgeBase = {
    update(a => h => d => f => i => {
      val predDef = defs(pred.name)

      val instantiated = predDef.instantiate(pred)
      val direct = PredicateCollector.collectDirectPredicates(instantiated, this)
      val folded = PredicateCollector.collectFoldedPredicates(instantiated, this)
      val pure = PredicateCollector.stripToPure(instantiated, this)

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


  def substituteRef(ref: ValRef, fresh: ValRef): KnowledgeBase = {
    KnowledgeBase(
      this.assignment,
      this.heap,
      this.direct,
      this.folded,
      this.info,
      this.partial
    )
  }

  private def mergeRefoldingStrategyOptions(strats: Seq[Option[RefoldingStrategy]]): Option[RefoldingStrategy] = {
    strats.foldLeft(Some(Seq[RefoldingStep]()).asInstanceOf[Option[Seq[RefoldingStep]]])(
        (acc, strat) => (acc, strat) match {
          case (Some(a), Some(s)) => Some(a ++ s.steps)
          case _ => None
        })
      .map(v => RefoldingStrategy(v))
  }

  private def attemptRefolding(defs: Map[String, PredDef], f: PredInstAccTerm): Option[RefoldingStrategy] = {
    val predDef = defs(f.pred.name)

    val instantiated = predDef.instantiate(f.pred)
    val direct = PredicateCollector.collectDirectPredicates(instantiated, this)
    val folded = PredicateCollector.collectFoldedPredicates(instantiated, this)
    val pure = PredicateCollector.stripToPure(instantiated, this)

    val mappedDirect = direct.map(d => findUnfoldingStrategy(defs, d))
    val mappedFolded = folded.map(f => findRefoldingStrategy(defs, f))

    mergeRefoldingStrategyOptions(mappedDirect ++ mappedFolded)
      .map(r => RefoldingStrategy(r.steps ++ Seq(FoldingStep(f.pred, f.perm))))
  }

  def findRefoldingStrategy(defs: Map[String, PredDef], f: PredInstAccTerm): Option[RefoldingStrategy] = {
    val current = this.folded.getAmount(f.pred)
    if (hasEnoughPermissions(f.perm, current)) {
      Some(RefoldingStrategy(Seq()))
    } else {
      // check if the predicate can be unfolded
      val unfolding = findUnfoldingStrategy(defs, f)
      // check if the predicate can be folded (potentially by unfolding some other predicate)
      val refolding = attemptRefolding(defs, f)
      (unfolding, refolding) match {
        case (Some(a), Some(b)) => Some(RefoldingStrategy(a.steps ++ b.steps))
        case (Some(a), None) => Some(a)
        case (None, Some(a)) => Some(a)
        case (None, None) => None
      }
    }
  }
}

trait RefoldingStep {
  def scale(f: Term): RefoldingStep

  def pretty(): String
}

case class UnfoldingStep(pred: PredInst, perm: Term, subs: Seq[RefoldingStep]) extends RefoldingStep {
  def scale(f: Term): RefoldingStep = {
    UnfoldingStep(this.pred, MulTerm(this.perm, f), this.subs.map(s => s.scale(f)))
  }

  def pretty(): String = {
    s"unfolding ${this.pred.pretty()} => ${this.perm.pretty()}\n${this.subs.map(_.pretty()).mkString("\n").indent(2)}"
  }
}

case class FoldingStep(pred: PredInst, perm: Term) extends RefoldingStep {
  def scale(f: Term): RefoldingStep = {
    FoldingStep(this.pred, MulTerm(this.perm, f))
  }

  def pretty(): String = {
    s"folding ${this.pred.pretty()}; ${this.perm.pretty()}"
  }
}

case class RefoldingStrategy(steps: Seq[RefoldingStep]) {
  def pretty(): String = {
    s"${this.steps.map(_.pretty()).mkString("\n")}"
  }
}

object PredicateCollector {
  def collectPotSatImpls(term: LogicTerm, kb: KnowledgeBase): Seq[ImplTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectPotSatImpls(a, kb) ++ collectPotSatImpls(b, kb)
      case impl@ImplTerm(prem, cons) => {
        if (kb.proveDetailed(prem) == PotSat) Seq(impl)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectPotSatImpls(t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectPotSatImpls(a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        val includedB = collectPotSatImpls(b, kb)
        if (includedB.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        Seq()
      }
      case _: PredFieldAccTerm => Seq()
      case _: PredInstAccTerm => Seq()
      case _: VarTerm => Seq()
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
      }
    }
  }


  def collectDirectPredicates(term: LogicTerm, kb: KnowledgeBase): Seq[PredFieldAccTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectDirectPredicates(a, kb) ++ collectDirectPredicates(b, kb)
      case ImplTerm(prem, cons) => {
        if (kb.prove(prem)) collectDirectPredicates(cons, kb)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectDirectPredicates(t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectDirectPredicates(a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        val includedB = collectDirectPredicates(b, kb)
        if (includedB.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        Seq()
      }
      case p: PredFieldAccTerm => Seq(p)
      case _: PredInstAccTerm => Seq()
      case _: VarTerm => Seq()
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
      }
    }
  }

  def stripToPure(term: LogicTerm, kb: KnowledgeBase): DNF = {
    term match {
      case BoolTerm(value) => {
        if (value) DNF(Set(Set()))
        else DNF(Set())
      }
      case v: EqCmpTerm => DNF(Set(Set(v)))
      case v: GreaterCmpTerm => DNF(Set(Set(v)))
      case v: GreaterEqCmpTerm => DNF(Set(Set(v)))
      case v: LessCmpTerm => DNF(Set(Set(v)))
      case v: LessEqCmpTerm => DNF(Set(Set(v)))
      case v: NotEqCmpTerm => DNF(Set(Set(v)))
      case AndTerm(a, b) => {
        val dnfA = stripToPure(a, kb)
        val dnfB = stripToPure(b, kb)
        dnfA.and(dnfB)
      }
      case ImplTerm(prem, cons) => {
        if (kb.prove(prem)) stripToPure(cons, kb)
        else DNF(Set(Set()))
      }
      case NotTerm(t) => {
        /*
        !((A & B & C) | (D & E & F))
        (!(A & B & C)) & (!(D & E & F))
        (!A | !B | !C) & (!D | !E | !F)
        (!A & !D | !B & !D | !C & !D) | (!A & !E | !B & !E | !C & !E) | (!A & !F | !B & !F | !C & !F)

        */
        stripToPure(t, kb).negate().prune()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val dnfA = stripToPure(a, kb)
        val dnfB = stripToPure(b, kb)
        dnfA.or(dnfB)
      }
      case _: PredFieldAccTerm => DNF(Set(Set()))
      case _: PredInstAccTerm => DNF(Set(Set()))
      case v: VarTerm => DNF(Set(Set(EqCmpTerm(v, BoolTerm(true)))))
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
      }
    }
  }


  def collectFoldedPredicates(term: LogicTerm, kb: KnowledgeBase): Seq[PredInstAccTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectFoldedPredicates(a, kb) ++ collectFoldedPredicates(b, kb)
      case ImplTerm(prem, cons) => {
        if (kb.prove(prem)) collectFoldedPredicates(cons, kb)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectFoldedPredicates(t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectFoldedPredicates(a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Predicates within disjunction!")
        }
        val includedB = collectFoldedPredicates(b, kb)
        if (includedB.nonEmpty) {
          throw new IllegalArgumentException("Predicates within disjunction!")
        }
        Seq()
      }
      case _: PredFieldAccTerm => Seq()
      case p: PredInstAccTerm => Seq(p)
      case _: VarTerm => Seq()
      case _ => {
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
      }
    }
  }
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

case class MethodInference(defs: Map[String, PredDef], reps: Map[String, InternalMethod], currentMethod: InternalMethod,
                           knowledge: mutable.HashMap[Ident, KnowledgeBase],
                           methSpec: mutable.HashMap[String, (Seq[LogicTerm], Seq[LogicTerm])],
                           injections: mutable.HashMap[Injection, Seq[RefoldingStrategy]]) {
  def merge(incoming: Seq[KnowledgeBase]): KnowledgeBase = {
    // TODO: maybe add a dedicated merge line which is takes care of this and makes merging more reliable

    println(s"merging:\n${incoming.map(k => k.pretty()).mkString(", ")}")

    // TODO: fix this
    incoming.head
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

  private def applyRefoldingStep(base: KnowledgeBase, step: RefoldingStep): KnowledgeBase = {
    step match {
      case FoldingStep(pred, perm) => {
        // if in the future the folding step has sub steps to fold other stuff beforehand then
        // insert the folding here before folding self

        // fold self
        base.fold(this.defs, pred, perm)
      }
      case UnfoldingStep(pred, perm, subs) => {
        // unfold the predicate on the current level
        val unfolded = base.unfold(this.defs, pred, perm)
        // unfold all the steps within this predicate
        // the substeps are scaled by the amount that the current unfolding actually unfolded
        subs.map(s => s.scale(perm))
          .foldLeft(unfolded)(applyRefoldingStep)
      }
      case c => {
        throw new IllegalArgumentException(s"Unable to process refolding step type ${c.getClass.getCanonicalName}")
      }
    }
  }

  private def applyRefoldingStrategy(inj: Injection, before: KnowledgeBase, strat: RefoldingStrategy): KnowledgeBase = {
    addRefoldingStrategiesToInjectionPoint(inj, Seq(strat))
    strat.steps.foldLeft(before)(applyRefoldingStep)
  }

  private def applyStrategies(inj: Injection, before: KnowledgeBase, strats: Seq[RefoldingStrategy]): KnowledgeBase = {
    strats.foldLeft(before)((kb, s) => applyRefoldingStrategy(inj, kb, s))
  }

  // TODO: maybe simplify the value ref computation and return option val ref to signal that a primitive type is returned
  private def computeValueRef(assignment: Assignment, heap: Heap, term: Term): (Assignment, Heap, ValRef) = {
    term match {
      case FieldAccTerm(src, field, typ) => {
        val (a, h, r) = computeValueRef(assignment, heap, src)
        val (hp, v) = h.lookupField(r, field)
        (a, hp, v)
      }
      case AddTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case IntTerm(value) => {
        val fresh = heap.rc.freshValRef()

        (assignment, heap, fresh)
      }
      case AndTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AndRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case NegTerm(t) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, t)

        val fresh = heap.rc.freshValRef()

        (a1, h1, fresh)
      }
      case NullTerm() => {
        val fresh = heap.rc.freshValRef()

        (assignment, heap, fresh)
      }
      case PermFracTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(PermFracRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case SubTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(SubRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case BoolTerm(value) => {
        val fresh = heap.rc.freshValRef()

        (assignment, heap, fresh)
      }
      case EqCmpTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case GreaterCmpTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case GreaterEqCmpTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case LessCmpTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case LessEqCmpTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case NotEqCmpTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case NotTerm(t) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, t)

        val fresh = heap.rc.freshValRef()

        (a1, h1, fresh)
      }
      case OrTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case VarTerm(name, _) => {
        val (a, r) = assignment.lookup(name)
        (a, heap, r)
      }
      case MulTerm(left, right) => {
        val (a1, h1, r1) = computeValueRef(assignment, heap, left)
        val (a2, h2, r2) = computeValueRef(a1, h1, right)

        val fresh = h2.rc.freshValRef()
        // TODO: record the equivalent constraints to specify the equivalences and retain as much knowledge
        // EqConst(AddRefs(r1, r2), fresh)

        (a2, h2, fresh)
      }
      case t => {
        throw new IllegalArgumentException(s"Unable to compute value ref of type ${t.getClass.getCanonicalName}")
      }
    }
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

  def processLine(before: KnowledgeBase, line: Line): (Boolean, KnowledgeBase) = {
    line match {
      case AssertLine(ln, inj, exp) => {
        clearInjection(inj)

        val folded = PredicateCollector.collectFoldedPredicates(exp, before)
        val direct = PredicateCollector.collectDirectPredicates(exp, before)
        val stripped = PredicateCollector.stripToPure(exp, before)

        val afterUnfolding = direct.foldLeft(before)((kb, d) => {
          kb.findUnfoldingStrategy(this.defs, d)
            .map(s => applyRefoldingStrategy(inj, kb, s))
            .getOrElse(kb)
        })

        val afterRefolding = folded.foldLeft(afterUnfolding)((kb, f) => {
          kb.findRefoldingStrategy(this.defs, f)
            .map(s => applyRefoldingStrategy(inj, kb, s))
            .getOrElse(kb)
        })

        (false, afterRefolding)
      }
      case AssumeLine(ln, exp) => {
        val stripped = PredicateCollector.stripToPure(exp, before)
        (false, before.update(a => h => d => f => i => {
          (a, h, d, f, i.and(stripped))
        }))
      }
        //      case BranchLine(ln, pre, cond, thn, els) =>
      case CallLine(ln, inj, method, targets, args) => {
        val initial = this.reps(method)
        val spec = this.methSpec(method)

        // exhale the pres in reverse order
        val extendedPres = initial.pres ++ spec._1
        val afterExhales = extendedPres.reverse.foldLeft(before)((kb, p) => {
          val strats = getRefoldingStrategiesAtInjectionPoint(inj)
          val (restart, result) = processLine(kb, ExhaleLine(ln, inj, p))
          val after = getRefoldingStrategiesAtInjectionPoint(inj)
          clearInjection(inj)
          addRefoldingStrategiesToInjectionPoint(inj, strats ++ after)
          result
        })

        // inhale the posts in correct order
        val extendedPosts = initial.posts ++ spec._2
        // TODO: fix restart flag stuff
        val afterInhales = extendedPosts.foldLeft(afterExhales)((kb, p) => processLine(kb, InhaleLine(ln, p))._2)

        (false, afterInhales)
      }
      case ExhaleLine(ln, inj, exp) => {
        clearInjection(inj)

        // TODO: check that all requirements are satisfied i.e. that all the field/pred permissions are provided
        //       -> generate and apply refolding strategies
        val folded = PredicateCollector.collectFoldedPredicates(exp, before)
        val direct = PredicateCollector.collectDirectPredicates(exp, before)
        val stripped = PredicateCollector.stripToPure(exp, before)

        val afterUnfolding = direct.foldLeft(before)((kb, d) => {
          kb.findUnfoldingStrategy(this.defs, d)
            .map(s => applyRefoldingStrategy(inj, kb, s))
            .getOrElse(kb)
        })

        val afterRefolding = folded.foldLeft(afterUnfolding)((kb, f) => {
          kb.findRefoldingStrategy(this.defs, f)
            .map(s => applyRefoldingStrategy(inj, kb, s))
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

        val reqsValue = collectRequiredFieldPermissions(value)
        //        val stratsValue = reqsValue.map(v => (v, before.findUnfoldingStrategy(this.defs, v)))
        //          .flatMap(v => v._2).toSeq
        //        val kb = applyStrategies(inj, before, stratsValue)

        // TODO: copy this part to the field assign
        val kb = reqsValue.foldLeft(before)((k, r) => {
          val strat = k.findUnfoldingStrategy(this.defs, r)
          strat.map(s => applyStrategies(inj, k, Seq(s))).getOrElse(k)
        })

        reqsValue.map(p => (p, kb.direct.getAmount(p.exp)))
          .filter(p => !kb.hasEnoughPermissions(p._1.perm, p._2))
          .foreach(p => propagateBackFieldPermReq(ln, p._1, p._2))

        val (a2, refBeforeAssign) = before.assignment.lookup(variable.name)
        val (a3, h3, valRef) = computeValueRef(a2, before.heap, value)
        val ua = a3.assign(variable.name, valRef)

        val ts = MapTermSub(Map((variable, VarTerm(s"t$$${refBeforeAssign.id}", variable.typ))))
        val subbedInfo = kb.info.substitute(ts).and(DNF(Set(Set(EqCmpTerm(variable, value)))))
        val resKb = KnowledgeBase(
          ua,
          h3,
          kb.direct.substitute(ts),
          kb.folded.substitute(ts),
          subbedInfo,
          kb.partial.substitute(ts)
        )
        (false, resKb)
      }
      case FieldAssignLine(ln, inj, fa, value) => {
        clearInjection(inj)

        // TODO: ensure that all requirements are satisfied/permissions are available(provable)
        // TODO: if needed add unfolding statements for the permissions
        // TODO: perform the substitution
        val reqs = collectRequiredFieldPermissions(fa.src)
        val self = Set(PredFieldAccTerm(fa, PermFracTerm(IntTerm(1), IntTerm(1))))

        // TODO: this can be improved by first searching for all strategies and then deciding which strategies should be executed
        //       -> iteratively improve current standing until final state reached
        val combined = reqs.union(self)
        val kbAfterTarget = combined.foldLeft(before)((k, r) => {
          val strat = k.findUnfoldingStrategy(this.defs, r)
          strat.map(s => applyStrategies(inj, k, Seq(s))).getOrElse(k)
        })

        val reqsValue = collectRequiredFieldPermissions(value)
        val kbAfterValue = reqsValue.foldLeft(kbAfterTarget)((k, r) => {
          val strat = k.findUnfoldingStrategy(this.defs, r)
          strat.map(s => applyStrategies(inj, k, Seq(s))).getOrElse(k)
        })

        val kb = kbAfterValue

        val stillMissingValue = reqsValue.map(p => (p, kb.direct.getAmount(p.exp)))
          .filter(p => !kb.hasEnoughPermissions(p._1.perm, p._2))

        val someSuccessWithPotential = stillMissingValue.map(a => findIfPotHasSolution(ln, kb, a._1, a._2))
          .exists(a => a)

        if (someSuccessWithPotential) {
          (true, kb)
        }
        else {
          val someSuccessWithDirectPropVal = stillMissingValue.map(p => propagateBackFieldPermReq(ln, p._1, p._2))
            .exists(a => a)
          if(someSuccessWithDirectPropVal){
            (true, kb)
          }
          else {
            val stillMissingTarget = combined.map(p => (p, kb.direct.getAmount(p.exp)))
              .filter(p => !kb.hasEnoughPermissions(p._1.perm, p._2))

            val someSuccessWithPotTarget = stillMissingTarget.map(a => findIfPotHasSolution(ln, kb, a._1, a._2)).exists(a => a)
            if(someSuccessWithPotTarget) {
              (true, kb)
            }
            else {
              val someSuccessWithDirectPropTarget = stillMissingTarget.map(p => propagateBackFieldPermReq(ln, p._1, p._2))
                .exists(a => a)

              if(someSuccessWithDirectPropTarget) {
                (true, kb)
              }
              else {
                val (a1, h1, valueRef) = computeValueRef(kb.assignment, kb.heap, value)

                val (a3, h3, objRef) = computeValueRef(a1, h1, fa.src)
                val (h4, fieldRef) = h3.lookupField(objRef, fa.field)
                val h5 = h4.assignField(objRef, fa.field, valueRef)
                // substitute the occurrences of this field usage with a temporary variable that refers to the val ref
                // TODO: THIS CAUSES PROBLEMS WITH ALIASED PERMISSIONS (e.g. in the make methods)
                //       INTRODUCE RENAMING SUBSTITUTIONS TO PREVENT THIS STUFF
                val ts = MapTermSub(Map((fa, VarTerm(s"t$$${fieldRef.id}", fa.typ))))
                val resKb = KnowledgeBase(
                  a3,
                  h5,
                  kb.direct.substitute(ts),
                  kb.folded.substitute(ts),
                  kb.info.substitute(ts),
                  kb.partial.substitute(ts)
                )

                (false, resKb)
              }
            }

          }
        }

      }
      case InhaleLine(ln, exp) => {
        val folded = PredicateCollector.collectFoldedPredicates(exp, before)
        val direct = PredicateCollector.collectDirectPredicates(exp, before)
        val stripped = PredicateCollector.stripToPure(exp, before)
        val partial = PredicateCollector.collectPotSatImpls(exp, before)
//        println(s"INHALING PARTIAL: ${partial}")
        val resKb = before.update((a, h, d, f, fac, pot) => {
          val ud = direct.foldLeft(d)((a, b) => a.inhale(b))
          val uf = folded.foldLeft(f)((a, b) => a.inhale(b))
          val ufac = fac.and(stripped)
          val up = pot.inhale(partial)
          (a, h, ud, uf, ufac, up)
        })

        val cleanedKb = cleanPotentialWithCurrentKnowledge(resKb)

        (false, cleanedKb)
      }
      case NewObjLine(ln, target, fields) => {
        // perform the assignment
        val (a2, refBeforeAssign) = before.assignment.lookup(target.name)
        val valRef = a2.rc.freshValRef()
        val ua = a2.assign(target.name, valRef)

        val afterAssign = KnowledgeBase(
          ua, before.heap, before.direct, before.folded, before.info, before.partial
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
            val info = i.substitute(ts)
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

  private def cleanPotentialWithCurrentKnowledge(resKb: KnowledgeBase): KnowledgeBase = {
    val sat = resKb.partial.partial.filter(p => resKb.proveDetailed(p.prem).equals(Sat))
      .map(p => p.cons)
    val unsat = resKb.partial.partial.filter(p => resKb.proveDetailed(p.prem).equals(UnSat))
    val potsat = resKb.partial.partial.filter(p => resKb.proveDetailed(p.prem).equals(PotSat))

    if(sat.isEmpty && unsat.isEmpty) {
      resKb
    }
    else {
      val redPot = resKb.update((a, h, d, f, i, _) => (a, h, d, f, i, Potential(potsat)))
      sat.foldLeft(redPot)((kb, r) => {
        val dirs = PredicateCollector.collectDirectPredicates(r, kb)
        val folds = PredicateCollector.collectFoldedPredicates(r, kb)
        val pots = PredicateCollector.collectPotSatImpls(r, kb)
        val pure = PredicateCollector.stripToPure(r, kb)
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
    val direct: Seq[Option[Set[LogicTerm]]] = PredicateCollector.collectDirectPredicates(impl.cons, kb)
      .filter(p => p.exp.equals(target.exp))
      .map(a => Some(Set[LogicTerm]()))
    val combined = if (depth > 0) {
      val folded = PredicateCollector.collectFoldedPredicates(impl.cons, kb)
        .map(p => {
          val predDef = this.defs(p.pred.name)
          val body = predDef.instantiate(p.pred)
          val impl = ImplTerm(BoolTerm(true), body)
          findRequiredKnowledge(kb, impl, target, depth - 1)
        })

      val pot = PredicateCollector.collectPotSatImpls(impl.cons, kb)
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
      val proofRes = this.knowledge(ident).proveDetailed(lp.toLT(payload))
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
        //        case NewObjLine(ln, target, fields) => {
        //          // check if target == term -> perfect since a fresh object is never null
        //          if (t.equals(target)) {
        //            true
        //          }
        //          else if (isJustFieldsOnVariable(t)) {
        //            false
        //            val (base, fields) = collectFieldsAndBaseVariable(t)
        //            if (base.equals(target)) {
        //              // problem since the fields are all null
        //              false
        //            }
        //            else {
        //
        //            }
        //          }
        //          else {
        //            // test if this term corresponds to a specific field of the object
        //            // otherwise reverse map the assignment of the variable and replace the temporary variables within the current term
        //            // TODO: fix this
        //          }
        //        }
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

  private def propagatePureConstraints(ident: Ident, pure: DNF): Boolean = {
    if (pure.clauses.size != 1) {
      throw new IllegalArgumentException(s"Expected single conjunction but got disjunction of pure terms! ${pure.toLogicTerm().pretty()}")
    }

    val preds = this.currentMethod.rep.getPredecessors(ident)
    println(s"ADDITIONAL REQUIREMENTS THAT NEED TO BE PROPAGATED!: ${pure.prune().pretty()}")
    if (preds.size == 1) {
      val pred = preds.head
      pure.clauses.head.map(p => {
          val (lp, pay) = getLinePropagator(p)
          val response = propagatePureConstraintThrough(pred, this.currentMethod.start, lp, pay)
          response match {
            case _: SuccessfulAdjustment[Term] => println(s"Successfully propagated constraint ${p}!")
            case _ => println("Unable to propagate constraint!")
          }
          response
        })
        .exists(a => a.isInstanceOf[SuccessfulAdjustment[Term]])
    }
    else {
      throw new IllegalArgumentException(s"Expected single predecessor of line got: ${preds.size}")
    }
  }

  private def findIfPotHasSolution(current: Ident, kb: KnowledgeBase, target: PredFieldAccTerm, amount: Term): Boolean = {
    val implSearchDepth = 10
    println(s"CHECKING IN IMPLICATIONS FOR: ${target.pretty()}")
    val reqs = kb.partial.partial.toSeq
      .flatMap(a => findRequiredKnowledge(kb, a, target, implSearchDepth))
      .foldLeft(Set[LogicTerm]())((a, b) => a.union(b))

    if (reqs.nonEmpty) {
      // TODO: joining like this would prevent something like: (A ==> REQ)  &  (!A ==> REQ)
      val pure = reqs.map(r => PredicateCollector.stripToPure(r, kb))
        .foldLeft(DNF(Set(Set())))((a, b) => a.and(b))
      propagatePureConstraints(current, pure)
    }
    else {
      false
    }
  }

  def infer(meth: InternalMethod) = {
    this.knowledge.clear()
    val counter = RefCounter(Counter(0))

    val mesh = meth.rep.mesh
    val lines = meth.rep.lines

    var restarting = true
    while(restarting){
      restarting = false

      // generate an initial assignment based of the arguments of the method
      val initAssignment = meth.args.foldLeft(new Assignment(counter))((a, f) => a.assign(f._1, counter.freshValRef()))
      val empty = KnowledgeBase(initAssignment, new Heap(counter), new DirectPermissionMask(), new FoldedPermissionMask(), DNF(Set(Set())), new Potential())

      // inhale the preconditions
      // TODO: fix the restart position
      val mergedPres = meth.pres ++ this.methSpec(this.currentMethod.method)._1
      val afterPres = mergedPres.foldLeft(empty)((kb, p) => processLine(kb, InhaleLine(meth.start, p))._2)
      this.knowledge.put(meth.start, afterPres)

      var open = mesh(meth.start).toSeq

      while (!restarting && open.nonEmpty) {
        val current = open.head
        println(s"processing line: ${current}")
        val kb = merge(mesh.filter(e => e._2.contains(current)).keys.map(this.knowledge).toSeq)

        val line = lines(current)
        println(s"line: ${line.pretty()}")

        val (shouldRestart, after) = processLine(kb, line)
        restarting = shouldRestart


        println(s":::::::::::::::: AFTER :::::::::::::::::")
        println(after.pretty())


        this.knowledge.put(current, after)

        open = open.tail ++ mesh(current).toSeq
      }

//      if(restarting){
//        println("RESTARTING")
//        println("RESTARTING")
//        println("RESTARTING")
//        println("RESTARTING")
//        println(this.methSpec(this.currentMethod.method))
////        throw new IllegalArgumentException("SUBBBBBBB")
//      }
    }

    // TODO: exhale post conditions
  }
}


case class Inference(defs: Map[String, PredDef], reps: Map[String, InternalMethod], program: Program, methSpec: mutable.HashMap[String, (Seq[LogicTerm], Seq[LogicTerm])]) {

  def printSpec(spec: (Seq[LogicTerm], Seq[LogicTerm])): Unit = {
    println("pres:")
    spec._1.foreach(e => println(e.pretty().indent(2)))
    println("posts:")
    spec._2.foreach(e => println(e.pretty().indent(2)))
  }

  def infer(): Unit = {
    // initialize empty additional specs for all methods
    this.reps.keySet.foreach(k => this.methSpec.put(k, (Seq(), Seq())))
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
      val mi = MethodInference(
        this.defs,
        this.reps,
        this.reps(f),
        new mutable.HashMap(),
        this.methSpec,
        new mutable.HashMap()
      )
      val beforeSpec = this.methSpec(f)
      mi.infer(this.reps(f))
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
    })

    println("::::::::::::::::::::: FULL ADD. SPEC. :::::::::::::::::")
    this.methSpec.foreach(e => {
      println(s"==== ${e._1} ====")
      printSpec(e._2)
    })
  }
}

// TODO: proof algorithm is too simple and does not support more suffisticated reasoning: y != null <==> null != y