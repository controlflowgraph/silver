package viper.silver.inference.v3

import viper.silver.ast.{
  AbstractAssign, AbstractDomainFuncApp, AbstractLocalVar, AccessPredicate, AnySetBinExp, AnySetExp, AnySetUnExp, Apply, Applying, Assert, Asserting, Assume, BackendFuncApp, BinExp, CondExp, DatatypeType, DebugLabelledOld, DomainBinExp, DomainFuncApp, DomainOpExp, DomainUnExp, EmptyMap, EmptyMultiset, EmptySeq, EmptySet, EqualityCmp, Exhale, Exists, Exp, ExplicitMap, ExplicitMultiset, ExplicitSeq, ExplicitSet, ExtensionStmt, FieldAccess, FieldAccessPredicate, FieldAssign, Fold, ForPerm, Forall, FuncApp, FuncLikeApp, Function, Goto, If, InferInfo, Inhale, InhaleExhaleExp, Injection, Label, LabelledOld, Let, Literal, LocalVar, LocalVarAssign, LocalVarDecl, LocalVarDeclStmt, LocalVarWithVersion, LocationAccess, MagicWand, MapCardinality, MapContains, MapDomain, MapExp, MapLookup, MapRange, MapUpdate, Maplet, Method, MethodCall, MultisetExp, NewStmt, Old, OldExp, Package, PermExp, PredicateAccess, PredicateAccessPredicate, Program, QuantifiedExp, Quasihavoc, Quasihavocall, RangeSeq, Ref, Result, SeqAppend, SeqContains, SeqDrop, SeqExp, SeqIndex, SeqLength, SeqTake, SeqUpdate, Seqn, SetExp, Stmt, Type, UnExp, Unfold, Unfolding, While
}
import viper.silver.inference.v3.ast._
import viper.silver.verifier.{Failure, Success, Verifier}

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

  def toVarName(): String = {
    s"t$$${this.id}"
  }

  def toVarTerm(typ: Type): VarTerm = {
    VarTerm(toVarName(), typ)
  }
}

case class Assignment(rc: RefCounter, variables: Map[String, (ValRef, Type)]) {
  def this(rc: RefCounter) = {
    this(rc, Map())
  }

  def assign(name: String, ref: ValRef, typ: Type): Assignment = {
    Assignment(this.rc, this.variables.updated(name, (ref, typ)))
  }

  def pretty(): String = {
    this.variables.map(e => s"${e._1}: ${e._2._1.pretty()} (${e._2._2})").mkString("\n")
  }

  def lookup(name: String, typ: Type): (Assignment, ValRef) = {
    if (this.variables.contains(name)) {
      (this, this.variables(name)._1)
    }
    else {
      val fresh = (this.rc.freshValRef(), typ)
      (Assignment(this.rc, this.variables.updated(name, fresh)), fresh._1)
    }
  }

  def variableNames: Seq[String] = {
    this.variables.keySet.toSeq
  }

  def getVariableTyp(name: String): Type = {
    this.variables(name)._2
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

case class Heap(rc: RefCounter, initialized: (Set[ValRef], Set[(ValRef, String, ValRef)]), objMap: Map[ValRef, Obj]) {

  def this(rc: RefCounter) = {
    this(rc, (Set(), Set()), Map())
  }

  private def lookup(ref: ValRef): (Heap, Obj) = {
    if (this.objMap.contains(ref)) {
      (this, this.objMap(ref))
    }
    else {
      val fresh = Obj(ref, Map())
      val ui = (this.initialized._1.union(Set(ref)), this.initialized._2)
      (Heap(this.rc, ui, this.objMap.updated(ref, fresh)), fresh)
    }
  }

  def pretty(): String = {
    s"${this.initialized}" + this.objMap.values.map(o => s"${o.ref.pretty()}:\n${o.fields.map(e => s"${e._1}: ${e._2.pretty()}").mkString("\n").indent(2)}".indent(2)).mkString("\n")
  }

  def lookupField(r: ValRef, field: String): (Heap, ValRef) = {
    val (h, o) = lookup(r)
    if (o.fields.contains(field)) {
      (h, o.fields(field))
    }
    else {
      val fresh = h.rc.freshValRef()
      val uo = o.assign(field, fresh)
      val initExtended = if (h.initialized._1.contains(r)) {
        (h.initialized._1.union(Set(fresh)), h.initialized._2.union(Set((r, field, fresh))))
      } else h.initialized
      (Heap(h.rc, initExtended, h.objMap.updated(r, uo)), fresh)
    }
  }

  def assignField(r: ValRef, field: String, v: ValRef): Heap = {
    Heap(this.rc, this.initialized, this.objMap.updated(r, this.objMap(r).assign(field, v)))
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

case class KnowledgeBase(assignment: Assignment, heap: Heap, direct: DirectPermissionMask, folded: FoldedPermissionMask, info: LogicTerm, partial: Potential, fieldTypes: Map[String, Type]) {

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
    KnowledgeBase(a, this.heap, this.direct, this.folded, this.info, this.partial, this.fieldTypes)
  }

  def withHeap(h: Heap): KnowledgeBase = {
    KnowledgeBase(this.assignment, h, this.direct, this.folded, this.info, this.partial, this.fieldTypes)
  }

  def update(fun: Assignment => Heap => DirectPermissionMask => FoldedPermissionMask => LogicTerm => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm)): KnowledgeBase = {
    update((a, h, d, f, i, p) => {
      val res = fun(a)(h)(d)(f)(i)
      (res._1, res._2, res._3, res._4, res._5, p)
    })
  }

  def update(f: (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential) => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, LogicTerm, Potential)): KnowledgeBase = {
    val res = f(this.assignment, this.heap, this.direct, this.folded, this.info, this.partial)
    KnowledgeBase(res._1, res._2, res._3, res._4, res._5, res._6, this.fieldTypes)
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
      case _ => {
        val proofResult = engine.prove(this, LessEqCmpTerm(amount, higher))
        proofResult == Sat
      }
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

  private def isClearlyZeroPerm(t: Term): Boolean = {
    TermRewriter.simplify(t) match {
      case PermFracTerm(IntTerm(a), _) => a.equals(BigInt.int2bigInt(0))
      case _ => true
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
        .toSeq

      val strats = mapped.flatMap(v => findUnfoldingStrategyInPredicate(engine, defs, fa, v))
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
  def collectPotSatImpls(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): Seq[ImplTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectPotSatImpls(engine, a, kb) ++ collectPotSatImpls(engine, b, kb)
      case impl@ImplTerm(prem, cons) => {
        if (engine.prove(kb, prem) == PotSat) Seq(impl)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectPotSatImpls(engine, t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectPotSatImpls(engine, a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        val includedB = collectPotSatImpls(engine, b, kb)
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


  def collectDirectPredicates(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): Seq[PredFieldAccTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectDirectPredicates(engine, a, kb) ++ collectDirectPredicates(engine, b, kb)
      case ImplTerm(prem, cons) => {
        if (engine.prove(kb, prem) == Sat) collectDirectPredicates(engine, cons, kb)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectDirectPredicates(engine, t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectDirectPredicates(engine, a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Field access predicates within disjunction!")
        }
        val includedB = collectDirectPredicates(engine, b, kb)
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

  def stripToPure(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): LogicTerm = {
    term match {
      case v: BoolTerm => v
      case v: EqCmpTerm => v
      case v: GreaterCmpTerm => v
      case v: GreaterEqCmpTerm => v
      case v: LessCmpTerm => v
      case v: LessEqCmpTerm => v
      case v: NotEqCmpTerm => v
      case AndTerm(a, b) =>
        val dnfA = stripToPure(engine, a, kb)
        val dnfB = stripToPure(engine, b, kb)
        AndTerm(dnfA, dnfB)
      case ImplTerm(prem, cons) => {
        if (engine.prove(kb, prem) == Sat) stripToPure(engine, cons, kb)
        else BoolTerm(true)
      }
      case NotTerm(t) => NotTerm(stripToPure(engine, t, kb))
      case OrTerm(a, b) =>
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val dnfA = stripToPure(engine, a, kb)
        val dnfB = stripToPure(engine, b, kb)
        OrTerm(dnfA, dnfB)
      case _: PredFieldAccTerm => BoolTerm(true)
      case _: PredInstAccTerm => BoolTerm(true)
      case v: VarTerm => EqCmpTerm(v, BoolTerm(true))
      case _ =>
        throw new IllegalArgumentException(s"Unable to extract folded predicates from logic term ${term.getClass.getCanonicalName}")
    }
  }


  def collectFoldedPredicates(engine: ReasoningEngine, term: LogicTerm, kb: KnowledgeBase): Seq[PredInstAccTerm] = {
    term match {
      case _: BoolTerm => Seq()
      case _: EqCmpTerm => Seq()
      case _: GreaterCmpTerm => Seq()
      case _: GreaterEqCmpTerm => Seq()
      case _: LessCmpTerm => Seq()
      case _: LessEqCmpTerm => Seq()
      case _: NotEqCmpTerm => Seq()
      case AndTerm(a, b) => collectFoldedPredicates(engine, a, kb) ++ collectFoldedPredicates(engine, b, kb)
      case ImplTerm(prem, cons) => {
        if (engine.prove(kb, prem) == Sat) collectFoldedPredicates(engine, cons, kb)
        else Seq()
      }
      case NotTerm(t) => {
        val included = collectFoldedPredicates(engine, t, kb)
        if (included.nonEmpty) {
          throw new IllegalArgumentException("Predicates within negation!")
        }
        Seq()
      }
      case OrTerm(a, b) => {
        // based on the assumption that viper does not support disjunctions with resource access stuff
        val includedA = collectFoldedPredicates(engine, a, kb)
        if (includedA.nonEmpty) {
          throw new IllegalArgumentException("Predicates within disjunction!")
        }
        val includedB = collectFoldedPredicates(engine, b, kb)
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

case class MethodInference(engine: ReasoningEngine,
                           defs: Map[String, PredDef], reps: Map[String, InternalMethod], currentMethod: InternalMethod,
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
    addRefoldingStrategiesToInjectionPoint(inj, Seq(strat))
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
    println(merged.toSeq.map(e => e._1.pretty() + " ==> " + e._2.pretty()))
    val ts = MapTermSub(merged)
    val f = ((t: Term) => t.substitute(ts))
    FixedPoint.compute(term, f)
  }

  def processLine(before: KnowledgeBase, line: Line): (Boolean, KnowledgeBase) = {
    line match {
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

        val (a2, refBeforeAssign) = before.assignment.lookup(variable.name, variable.typ)
        val normKb = before.withAssignment(a2)
        val (kbN, refN, typN, infoN) = TermNormalization.computeNormalizedValueRef(normKb, normKb.assignment.rc, value)
        val ua = kbN.assignment.assign(variable.name, refN, variable.typ)

        val ts = MapTermSub(Map((variable, refBeforeAssign.toVarTerm(variable.typ))))
        val subbedInfo = kb.info.substitute(ts).asInstanceOf[LogicTerm] //.and(EqCmpTerm(variable, ))
        val resKb = KnowledgeBase(
          ua,
          kbN.heap,
          kbN.direct.substitute(ts),
          kbN.folded.substitute(ts),
          subbedInfo.and(infoN),
          kbN.partial.substitute(ts),
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
              println(stillMissingTarget)
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
                  kbS.assignment,
                  h5,
                  kb.direct.substitute(ts),
                  kb.folded.substitute(ts),
                  kb.info.substitute(ts).asInstanceOf[LogicTerm].and(infoN).and(infoS),
                  kb.partial.substitute(ts),
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

        val (kb1, folded) = normalizeFoldedRequirements(before, rawFolded)
        val (kb2, direct) = normalizeDirectRequirements(kb1, rawDirect)
        val (kb3, stripped) = normalizeLogicTerm(kb2, rawStripped)
        val (kb4, partial) = normalizePotentialRequirements(kb3, rawPartial)


        // TODO: normalize the folded, direct, partial and stripped (EVERYWHERE)
        val resKb = kb4.update((a, h, d, f, fac, pot) => {
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
        val (a2, refBeforeAssign) = before.assignment.lookup(target.name, target.typ)
        val valRef = a2.rc.freshValRef()
        val ua = a2.assign(target.name, valRef, target.typ)

        val afterAssign = KnowledgeBase(
          ua, before.heap, before.direct, before.folded, before.info, before.partial, before.fieldTypes
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
      val (resKb, args) = normalizeTermList(before, r.pred.args)
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
      val base = this.knowledge(ident)
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
      val empty = KnowledgeBase(initAssignment, new Heap(counter), new DirectPermissionMask(), new FoldedPermissionMask(), BoolTerm(true), new Potential(), fieldTypes)

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


        if (restarting) {
          throw new IllegalArgumentException(s"RESTARTING :/ ${line.pretty()}")
        }
      }

      if (!restarting) {
        // TODO: perform posts in reverse order
        val mergedPosts = (meth.posts ++ this.methSpec(this.currentMethod.method)._2).reverse

        val finInj = this.currentMethod.finalInj
        val finalKb = this.knowledge(meth.stop)

        val startKb = this.knowledge(meth.start)
        on(engine, startKb, finalKb, meth)

        val afterPosts = mergedPosts.foldLeft(finalKb)((kb, p) => processLine(kb, ExhaleLine(meth.stop, finInj, p))._2)
//        this.knowledge.put(meth.stop, afterPosts)
        // TODO: extend the post conditions with the information that are left over
      }
    }
  }

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
      case NotTerm(t) => computeNormalizedUnaryOperator(kb, counter, viper.silver.ast.Bool, t, (v) => NotTerm(v.asInstanceOf[LogicTerm]))
      case OrTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Bool, a, b, (a, b) => OrTerm(a.asInstanceOf[LogicTerm], b.asInstanceOf[LogicTerm]))
      case VarTerm(name, typ) => {
        val lookupResult = kb.assignment.lookup(name, typ)
        val valRef = lookupResult._2
        val ukb = kb.withAssignment(lookupResult._1)
        (ukb, valRef, typ, BoolTerm(true))
      }
      case c => {
        throw new IllegalArgumentException(s"Unable to compute normalized form for logic term of type ${c.getClass.getCanonicalName}")
      }
    }
  }

  def computeNormalizedValueRef(kb: KnowledgeBase, counter: RefCounter, term: Term): (KnowledgeBase, ValRef, Type, LogicTerm) = {
    term match {
      case FieldAccTerm(src, field, typ) => {
        val (kbS, refS, typS, infoS) = computeNormalizedValueRef(kb, counter, src)
        val (h, ref) = kbS.heap.lookupField(refS, field)
        val resKb = kbS.withHeap(h)
        (resKb, ref, kb.fieldTypes(field), infoS)
      }
      case AddTerm(a, b) => {
        val intTyp: Type = viper.silver.ast.Int
        val permTyp: Type = viper.silver.ast.Perm
        val mapping = Seq(
          ((intTyp, intTyp), intTyp),
          ((permTyp, permTyp), permTyp)
        ).toMap
        computeNormalizedBinaryOperatorWithTypeMapping(kb, counter, mapping, a, b, AddTerm)
      }
      case lit: IntTerm => computeNormalizedLiteral(kb, counter, viper.silver.ast.Int, lit)
      case lt: LogicTerm => computeNormalizedLogicTerm(kb, counter, lt)
      case MulTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Int, a, b, MulTerm)
      case NegTerm(t) => computeNormalizedUnaryOperator(kb, counter, viper.silver.ast.Int, t, NegTerm)
      case lit: NullTerm => computeNormalizedLiteral(kb, counter, viper.silver.ast.Ref, lit)
        // TODO: the ADD etc are overloaded with respect to their type so it needs to be checked which res type actually is taken
        //       perm + int => ERROR
        //       perm * int => perm
        //       int * int => int
        //       -perm => perm
        //       !bool => bool
        //       ...
      case PermFracTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Perm, a, b, PermFracTerm)
      case SubTerm(a, b) => computeNormalizedBinaryOperator(kb, counter, viper.silver.ast.Int, a, b, SubTerm)
      case c => {
        throw new IllegalArgumentException(s"Unable to compute normalized form for term of type ${c.getClass.getCanonicalName}")
      }
    }
  }
}

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

    //    println("PROOF SPEC:")
    //    println(body)

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