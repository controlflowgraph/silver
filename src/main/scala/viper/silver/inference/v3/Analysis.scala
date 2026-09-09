package viper.silver.inference.v3

import viper.silver.ast.{AbstractAssign, AbstractDomainFuncApp, AbstractLocalVar, AccessPredicate, AnySetBinExp, AnySetExp, AnySetUnExp, Apply, Applying, Assert, Asserting, Assume, BackendFuncApp, BinExp, CondExp, DebugLabelledOld, DomainBinExp, DomainFuncApp, DomainOpExp, DomainUnExp, EmptyMap, EmptyMultiset, EmptySeq, EmptySet, EqualityCmp, Exhale, Exists, Exp, ExplicitMap, ExplicitMultiset, ExplicitSeq, ExplicitSet, ExtensionStmt, FieldAccess, FieldAccessPredicate, FieldAssign, Fold, ForPerm, Forall, FuncApp, FuncLikeApp, Function, Goto, If, Inhale, InhaleExhaleExp, Injection, Label, LabelledOld, Let, Literal, LocalVar, LocalVarAssign, LocalVarDecl, LocalVarDeclStmt, LocalVarWithVersion, LocationAccess, MagicWand, MapCardinality, MapContains, MapDomain, MapExp, MapLookup, MapRange, MapUpdate, Maplet, Method, MethodCall, MultisetExp, NewStmt, Old, OldExp, Package, PermExp, PredicateAccess, PredicateAccessPredicate, QuantifiedExp, Quasihavoc, Quasihavocall, RangeSeq, Ref, Result, SeqAppend, SeqContains, SeqDrop, SeqExp, SeqIndex, SeqLength, SeqTake, SeqUpdate, Seqn, SetExp, Stmt, UnExp, Unfold, Unfolding, While}
import viper.silver.inference.v3.ast.{CallLine, FieldAssignLine, InternalMethod}

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
      case _: PermExp => false // TODO: fix if perm exp could have rec func call
      case access: LocationAccess => access match {
        case FieldAccess(rcv, _) => containsRecursiveFunctionCall(rcv, func)
        case PredicateAccess(args, _) => args.exists(a => containsRecursiveFunctionCall(a, func))
      }
      case CondExp(cond, thn, els) => containsRecursiveFunctionCall(cond, func) || containsRecursiveFunctionCall(thn, func) || containsRecursiveFunctionCall(els, func)
      case Unfolding(_, body) => containsRecursiveFunctionCall(body, func)
      case Applying(_, body) => containsRecursiveFunctionCall(body, func)
      case Asserting(_, body) => containsRecursiveFunctionCall(body, func)
      case Let(_, exp, body) => containsRecursiveFunctionCall(exp, func) || containsRecursiveFunctionCall(body, func)
      case exp: QuantifiedExp => exp match {
        case Forall(_, _, exp) => containsRecursiveFunctionCall(exp, func)
        case Exists(_, _, exp) => containsRecursiveFunctionCall(exp, func)
        case ForPerm(_, _, body) => containsRecursiveFunctionCall(body, func)
      }
      case ForPerm(_, _, body) => containsRecursiveFunctionCall(body, func)
      case localVar: AbstractLocalVar => localVar match {
        case LocalVar(_, _) => false
        case Result(_) => false
        case LocalVarWithVersion(_, _) => false
      }
      case exp: SeqExp => exp match {
        case EmptySeq(_) => false
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
        case EmptySet(_) => false
        case ExplicitSet(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
      }
      case exp: MultisetExp => exp match {
        case exp: AnySetExp => exp match {
          case exp: AnySetUnExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case exp: AnySetBinExp => exp.args.exists(a => containsRecursiveFunctionCall(a, func))
          case MapDomain(base) => containsRecursiveFunctionCall(base, func)
          case MapRange(base) => containsRecursiveFunctionCall(base, func)
        }
        case EmptyMultiset(_) => false
        case ExplicitMultiset(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
      }
      case exp: MapExp => exp match {
        case EmptyMap(_, _) => false
        case ExplicitMap(elems) => elems.exists(e => containsRecursiveFunctionCall(e, func))
        case Maplet(key, value) => containsRecursiveFunctionCall(key, func) || containsRecursiveFunctionCall(value, func)
        case MapUpdate(base, key, value) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func) || containsRecursiveFunctionCall(value, func)
        case MapLookup(base, key) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func)
        case MapContains(key, base) => containsRecursiveFunctionCall(base, func) || containsRecursiveFunctionCall(key, func)
        case MapCardinality(base) => containsRecursiveFunctionCall(base, func)
      }
      case _: Literal => false
      case DomainFuncApp(funcname, args, _) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
      case app: FuncLikeApp => app match {
        case FuncApp(funcname, args) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
        case app: AbstractDomainFuncApp => app match {
          case DomainFuncApp(funcname, args, _) => func.contains(funcname) || args.exists(a => containsRecursiveFunctionCall(a, func))
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
          case LabelledOld(exp, _) => containsRecursiveFunctionCall(exp, func)
          case DebugLabelledOld(exp, _) => containsRecursiveFunctionCall(exp, func)
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
          case FieldAccess(_, _) => Set(exp)
          case _ => Set()
        }
          //        case access: ResourceAccess =>
        case CondExp(cond, thn, els) =>
          if (containsRecursiveFunctionCall(cond, func)) Set()
          else computeFunctionBaseCases(thn, func).union(computeFunctionBaseCases(els, func))
        case Let(_, exp, body) =>
          if (containsRecursiveFunctionCall(exp, func)) Set()
          else computeFunctionBaseCases(body, func)
          //        case exp: QuantifiedExp =>
          //        case ForPerm(variables, resource, body) =>
        case _: AbstractLocalVar => Set()
        case _: SeqExp => Set()
        case _: SetExp => Set()
        case _: MultisetExp => Set()
        case _: MapExp => Set()
        case _: Literal => Set()
          //        case trigger: PossibleTrigger =>
          //        case trigger: ForbiddenInTrigger =>
        case FuncApp(_, _) => Set()
        case _: BinExp => Set() // TODO: maybe refine this if there is a use for different base cases
        case _: UnExp => Set() // TODO: maybe refine this if there is a use for different base cases
          //        case lhs: Lhs =>
          //        case exp: ExtensionExp =>
      }
  }


  private def computeExprRep(stmt: Stmt, resultVariable: String, recursive: String): Option[Exp] = {
    stmt match {
      case NewStmt(_, _) => None
      case assign: AbstractAssign => assign match {
        case LocalVarAssign(lhs, rhs) =>
          if (lhs.name.equals(resultVariable))
            Some(rhs)
          else None
        case FieldAssign(_, _) => None
      }
      case c@MethodCall(methodName, args, targets) =>
        if (methodName.equals(recursive))
          Some(FuncApp("Func$" + recursive, args)(c.pos, c.info, targets.head.typ, c.errT))
        else None
      case Exhale(_) => None
      case Inhale(_) => None
      case Assert(_) => None
      case Assume(_) => None
        // TODO: maybe this part can be ignored instead of producing none result when doing the functionalization
      case Fold(_) => None
      case Unfold(_) => None
      case Package(_, _) => None
      case Apply(_) => None
      case Seqn(ss, _) =>
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
                case l@LocalVarAssign(lhs, rhs) =>
                  Some(Let(LocalVarDecl(lhs.name, lhs.typ)(lhs.pos, lhs.info, lhs.errT),
                    rhs,
                    m
                  )(l.pos, l.info, l.errT))
                  // case Seqn(ss, scopedSeqnDeclarations) => TODO: allow nesting of sequences although this might not be relevant
                  // case If(cond, thn, els) => TODO: potentially allow this if there is a usecase / valid mapping
                case _ => None
              }
            }
          ))
        }
      case i@If(cond, thn, els) =>
        val expA = computeExprRep(thn, resultVariable, recursive)
        val expB = computeExprRep(els, resultVariable, recursive)
        (expA, expB) match {
          case (Some(a), Some(b)) => Some(CondExp(cond, a, b)(i.pos, i.info, i.errT))
          case _ => None
        }
      case Injection(_) => None
      case While(_, _, _) => None
      case Label(_, _) => None
      case Goto(_) => None
      case LocalVarDeclStmt(_) => None // TODO: check if this comes up and needs to be handled gracefully
      case Quasihavoc(_, _) => None
      case Quasihavocall(_, _, _) => None
      case _: ExtensionStmt => None
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