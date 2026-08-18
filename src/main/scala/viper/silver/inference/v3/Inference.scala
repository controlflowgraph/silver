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

case class Assignment(variables: Map[String, ValRef]) {
  def this() = {
    this(Map())
  }

  def assign(name: String, ref: ValRef): Assignment = {
    Assignment(this.variables.updated(name, ref))
  }

  def pretty(): String = {
    this.variables.map(e => s"${e._1}: ${e._2.pretty()}").mkString("\n")
  }
}


case class RefCounter(counter: Counter) {
  def freshValRef(): ValRef = {
    ValRef(this.counter.next())
  }
}

case class Obj(ref: ValRef, fields: Map[String, ValRef]) {
  def lookup(counter: Counter, field: String) = {

  }
}

case class Heap(objMap: Map[ValRef, Obj]) {

  def this() = {
    this(Map())
  }

  def pretty(): String = {
    this.objMap.values.map(o => s"${o.ref.pretty()}: ${o.fields.map(e => s"${e._1}: ${e._2.pretty()}").mkString("\n").indent(2)}".indent(2)).mkString("\n")
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

  def exhale(pred: PredInst, perm: Term): FoldedPermissionMask = {
    val current = this.permissions.getOrElse(pred, PermFracTerm(IntTerm(0), IntTerm(1)))
    val amount = TermRewriter.simplify(SubTerm(current, perm))
    FoldedPermissionMask(
      this.permissions.updated(pred, amount)
    )
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
}

case class KnowledgeBase(assignment: Assignment, heap: Heap, direct: DirectPermissionMask, folded: FoldedPermissionMask, facts: DNF) {

  def prove(term: LogicTerm): Boolean = {
    false
  }

  def update(f: Assignment => Heap => DirectPermissionMask => FoldedPermissionMask => DNF => (Assignment, Heap, DirectPermissionMask, FoldedPermissionMask, DNF)): KnowledgeBase = {
    val res = f(this.assignment)(this.heap)(this.direct)(this.folded)(this.facts)
    KnowledgeBase(res._1, res._2, res._3, res._4, res._5)
  }

  def pretty(): String = {
    val prettyHeap = this.heap.pretty().indent(2)
    val prettyAssignment = this.assignment.pretty().indent(2)
    val prettyDirect = this.direct.pretty().indent(2)
    val prettyFolded = this.folded.pretty().indent(2)
    val prettyDNF = this.facts.pretty().indent(2)
    s"assignment:\n$prettyAssignment\nheap:\n$prettyHeap\ndirect:\n$prettyDirect\nfolded:\n$prettyFolded\nfacts:\n$prettyDNF"
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

  private def searchDepth: Int = 10
//
//  private def findContainedFieldPermission(defs: Map[String, PredDef], pred: PredInst, req: FieldAccTerm): Seq[RefoldingStrategy] = {
//    findContainedFieldPermission(defs, pred, req, 0)
//  }
//
//  private def findContainedFieldPermission(defs: Map[String, PredDef], preds: Seq[PredInstAccTerm], req: FieldAccTerm, currentDepth: Int): Seq[RefoldingStrategy] = {
//    preds.flatMap(v => findContainedFieldPermission(defs, v.pred, req, currentDepth - 1)
//      .map(_.scale(v.perm)))
//  }
//
//  private def findContainedFieldPermission(defs: Map[String, PredDef], pred: PredInst, req: FieldAccTerm, currentDepth: Int): Seq[RefoldingStrategy] = {
//    val res = defs(pred.name)
//    val argSub = res.params.zip(pred.args).toMap
//    val ts = FuncTermSub {
//      case t@VarTerm(v, _) => argSub.getOrElse(v, t)
//      case v => v
//    }
//    val subbed = res.body.substitute(ts).asInstanceOf[LogicTerm]
//    val base = PredicateCollector.collectDirectPredicates(subbed, this)
//      .filter(f => f.pred.equals(req))
//      .map(t => RefoldingStrategy(Seq(RefoldingStep(unfolding = true, pred)), t.perm))
//    val extended = if (currentDepth < searchDepth) {
//      val folded = PredicateCollector.collectFoldedPredicates(subbed, this)
//      findContainedFieldPermission(defs, folded, req, currentDepth - 1)
//        .map(v => v.prepend(Seq(RefoldingStep(unfolding = true, pred))))
//    }
//    else Seq()
//    // TODO: when unfolding the algorithm would need to consider the pure knowledge that is included in implications
//    // TODO: the perm amounts for the different
//    base ++ extended
//  }

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

    if(containedOnDirectLevel || containedOnSubLevel){
      Some(UnfoldingStep(instance.pred, instance.perm, subs))
    }
    else {
      None
    }
  }

  def findUnfoldingStrategy(defs: Map[String, PredDef], fa: PredFieldAccTerm): Option[RefoldingStrategy] = {
    // TODO: check if it is even possible that the permission amount is reachable
    val directAmount = this.direct.getAmount(fa.exp)
    if (hasEnoughPermissions(fa.perm, directAmount)) {
      println(s"HAS ENOUGH PERMISSIONS FOR: ${fa.pretty()}")
      Some(RefoldingStrategy(Seq()))
    }
    else {
      // TODO: find the unfolding strategy
      val mapped: Seq[PredInstAccTerm] = this.folded.permissions.map(e => PredInstAccTerm(e._1, e._2)).toSeq

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


case class Inference(defs: Map[String, PredDef], reps: Map[String, InternalMethod], program: Program) {

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
        // fold subs first
        // fold self
        throw new RuntimeException("Not implemented! (folding step processing)")
      }
      case UnfoldingStep(pred, perm, subs) => {
        // unfold the predicate on the current level
        val unfolded = base.unfold(this.defs, pred, perm)
        // unfold all the steps within this predicate
        subs.foldLeft(unfolded)(applyRefoldingStep)
      }
      case c => {
        throw new IllegalArgumentException(s"Unable to process refolding step type ${c.getClass.getCanonicalName}")
      }
    }
  }

  private def applyRefoldingStrategy(before: KnowledgeBase, strat: RefoldingStrategy): KnowledgeBase = {
    strat.steps.foldLeft(before)(applyRefoldingStep)
  }

  private def applyStrategies(before: KnowledgeBase, strats: Seq[RefoldingStrategy]): KnowledgeBase = {
    strats.foldLeft(before)(applyRefoldingStrategy)
  }

  def processLine(before: KnowledgeBase, line: Line): KnowledgeBase = {
    line match {
      //      case AssertLine(ln, inj, exp) =>
      //      case AssumeLine(ln, exp) =>
      //      case BranchLine(ln, pre, cond, thn, els) =>
      //      case CallLine(ln, inj, method, targets, args) =>
      //      case ExhaleLine(ln, inj, exp) =>
      case FieldAssignLine(ln, inj, fa, value) => {
        // TODO: ensure that all requirements are satisfied/permissions are available(provable)
        // TODO: if needed add unfolding statements for the permissions
        // TODO: perform the substitution
        val reqs = collectRequiredFieldPermissions(fa.src)
        val self = Set(PredFieldAccTerm(fa, PermFracTerm(IntTerm(1), IntTerm(1))))
        //        println(s"REQUIREMENTS FROM SUB: ${reqs}")
        //        println(s"REQUIREMENTS FROM SELF: ${self}")
        // FIRST SEARCH ALL THE UNFOLDING STRATEGIES
        // THEN DETERMINE THE MAXIMUM REQUIRED AMOUNTS FOR EACH UNFOLD
        val combined = reqs.union(self)
        val stratsTarget = combined.map(v => (v, before.findUnfoldingStrategy(this.defs, v)))
        //          .foreach(s => println(s"${s._1.pretty()} => ${s._2}"))

        val reqsValue = collectRequiredFieldPermissions(value)
        val stratsValue = reqsValue.map(v => (v, before.findUnfoldingStrategy(this.defs, v)))
        //          .foreach(s => println(s"${s._1.pretty()} => ${s._2}"))

        // apply all the unfolding strategies
        // this can be refined with better implementations at some point in time :)
        val combinedStrats = (stratsTarget ++ stratsValue).flatMap(v => v._2).toSeq

        applyStrategies(before, combinedStrats)
      }
      case InhaleLine(ln, exp) => {
        val folded = PredicateCollector.collectFoldedPredicates(exp, before)
        val direct = PredicateCollector.collectDirectPredicates(exp, before)
        val stripped = PredicateCollector.stripToPure(exp, before)
        before.update(a => h => d => f => fac => {
          val ud = direct.foldLeft(d)((a, b) => a.inhale(b))
          val uf = folded.foldLeft(f)((a, b) => a.inhale(b))
          val ufac = fac.and(stripped)
          (a, h, ud, uf, ufac)
        })
      }
        //      case LocalAssignLine(ln, inj, variable, value) =>
      case l => {
        throw new IllegalArgumentException(s"Unable to process line type ${l.getClass.getCanonicalName}")
      }
    }
  }

  def infer(meth: InternalMethod) = {
    // TODO: add multiplication processing to the term rewriter
    val counter = Counter(0)
    val knowledge = mutable.HashMap[Ident, KnowledgeBase]()
    val initAssignment = meth.args.foldLeft(new Assignment())((a, f) => a.assign(f._1, {
      val c = counter.next()
      ValRef(c)
    }))
    knowledge.put(meth.start, KnowledgeBase(initAssignment, new Heap(), new DirectPermissionMask(), new FoldedPermissionMask(), DNF(Set(Set()))))

    val mesh = meth.rep.mesh
    val lines = meth.rep.lines
    var open = mesh(meth.start).toSeq
    while (open.nonEmpty) {
      val current = open.head
      println(s"processing line: ${current}")
      val kb = merge(mesh.filter(e => e._2.contains(current)).keys.map(knowledge).toSeq)

      val line = lines(current)
      println(s"line: ${line.pretty()}")

      val after = processLine(kb, line)

      println(s":::::::::::::::: AFTER :::::::::::::::::")
      println(after.pretty())


      knowledge.put(current, after)

      open = open.tail ++ mesh(current).toSeq
    }
  }

  def infer(): Unit = {
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
      infer(this.reps(f))
    })
  }
}