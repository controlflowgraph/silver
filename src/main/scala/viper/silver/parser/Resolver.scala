// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import viper.silver.FastMessaging
import viper.silver.parser.PKw.Requires
import viper.silver.parser.PSymOp.{EqEq, Ne}

import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.collection.mutable

/**
 * A resolver and type-checker for the intermediate Viper AST.
 */
case class Resolver(p: PProgram) {
  val names = NameAnalyser()
  val typechecker = TypeChecker(p, names)

  def run(warnAboutFunctionPermAmounts: Boolean): Option[PProgram] = {
    val nameSuccess = names.run(p)
    // Run typechecker even if name resolution failed, to add more information to the
    // program, and report any other errors. A name resolution error should not cause
    // a typechecker error however!
    val typeckSuccess = try {
      typechecker.run(p, warnAboutFunctionPermAmounts)
    } catch {
      case e: Throwable =>
        // TODO: remove this try/catch once all assumptions that
        // name resolution succeeded are removed from the type checker
        val frame = e.getStackTrace().find(!_.getClassName().startsWith("scala")).map(_.toString()).getOrElse("")
        val msg = s"internal error during typechecking. Please file a bug report at https://github.com/viperproject/silver. Error \"${e.toString()}\" at \"$frame\""
        typechecker.messages ++= FastMessaging.message(p, msg)
        e.printStackTrace()
        false
    }
    if (nameSuccess && typeckSuccess)
      Some(p)
    else
      None
  }

  def messages = names.messages ++ typechecker.messages // ++ Consistency.messages // shouldn't be needed - Consistency errors should be generated only in later phases.
}

/**
 * Performs type-checking and sets the type of all typed nodes.
 */
case class TypeChecker(program: PProgram, names: NameAnalyser) {

  def this(names: NameAnalyser) = {
    this(null, names)
  }

  import TypeHelper._

  var curMember: PScope = null
  var curFunction: PFunction = null
  var resultAllowed: Boolean = false
  var permBan: Option[String] = None
  var warnAboutFunctionPermAmounts: Boolean = false

  /** to record error messages */
  var messages: FastMessaging.Messages = Nil

  def success: Boolean = messages.isEmpty || messages.forall(m => !m.error)

  def run(p: PProgram, warnAboutFunctionPermAmounts: Boolean): Boolean = {
    this.warnAboutFunctionPermAmounts = warnAboutFunctionPermAmounts
    check(p)
    success
  }

  def check(p: PProgram): Unit = {
    println(p)

    /* [2022-03-14 Alessandro] Domain function declarations, method declarations and ordinary function declarations
     * must be checked before their application is checked. Especially, this is because type variables in signatures
     * must be resolved. However, the checks in the following block are independent of each other.
     */
    p.datatypes foreach checkDatatype
    p.domains foreach checkFunctions
    p.fields foreach check
    p.functions foreach checkDeclaration
    p.predicates foreach checkDeclaration
    p.methods foreach checkDeclaration

    /* [2022-03-14 Alessandro] Unfortunately, there is currently no mechanism of checking some extensions "signature" first
     * and checking its "body" in a later step. However, there are currently no Extensions planned that would use this
     * functionality. Hence we check all the extensions after declarations and signatures are checked. This allows
     * extensions in which there are function, domain function and method applications.
     */
    p.extensions foreach checkExtension

    /* [2022-03-14 Alessandro]
     * The following block of checks must occur after declarations and signatures are checked, but the checks in the block
     * do not depend on each other. Note that extensions are checked beforehand, which allow function and method alike extensions.
     */
    p.domains foreach checkAxioms
    p.functions foreach checkBody
    p.predicates foreach checkBody
    p.methods foreach checkBody
  }

  def checkMember(m: PScope)(fcheck: => Unit): Unit = {
    val oldCurMember = curMember
    curMember = m
    fcheck
    curMember = oldCurMember
  }

  def checkUniqueness[T](elems: Seq[T], loc: PNode, ctx: String, form: T => String): Unit = {
    var duplicate: Set[T] = Set()
    var current: Seq[T] = elems
    while (current != Nil) {

      if (current.tail.contains(current.head)) {
        duplicate = duplicate.union(Set(current.head))
      }
      current = current.tail
    }

    duplicate.foreach(d => {
      messages ++= FastMessaging.message(loc, s"duplicate element `${form(d)}` in ${ctx}")
    })
  }

  def checkDatatype(d: PDatatype): Unit = {
    checkMember(d) {
      // TODO CFG: check the datatype
      checkUniqueness[PTypeVarDecl](d.typVars.map(c => c.inner.toSeq).getOrElse(Nil), d, s"generic parameters of `${d.idndef.name}`", v => v.idndef.name)
      checkUniqueness[String](d.containedFieldDecls.map(c => c.idndef.name), d, s"field names of `${d.idndef.name}`", v => v.replaceFirst(d.idndef.name + "\\$", ""))
      // checking the types of the fields so they are resolved
      d.containedFields.flatMap(f => f.fields.toSeq)
        .foreach(c => check(c.typ))
    }
  }

  def checkDeclaration(m: PMethod): Unit = {
    checkMember(m) {
      // TODO CFG: check that all generic parameters are defined in the arguments and return type
      (m.formalArgs ++ m.formalReturns) foreach (a => check(a.typ))
    }
  }

  def checkBody(m: PMethod): Unit = {
    checkMember(m) {
      m.pres.toSeq foreach (p => {
        check(p.e, Impure)
        checkNoPermForpermExceptInhaleExhale(p.e)
      })
      m.posts.toSeq foreach (p => {
        check(p.e, Impure)
        checkNoPermForpermExceptInhaleExhale(p.e)
      })
      m.body.foreach(check)
    }
  }

  def checkDeclaration(f: PFunction): Unit = {
    checkMember(f) {
      assert(curFunction == null)
      curFunction = f
      f.formalArgs foreach (a => check(a.typ))
      check(f.typ)
      curFunction = null
    }
  }

  def checkBody(f: PFunction): Unit = {
    checkMember(f) {
      assert(curFunction == null)
      curFunction = f
      f.pres.toSeq foreach (p => {
        check(p.e, Impure)
        checkNoPermForpermExceptInhaleExhale(p.e)
        checkNoMagicWands(p.e)
      })
      permBan = Some("function postconditions")
      resultAllowed = true
      f.posts.toSeq foreach (p => {
        check(p.e, Bool)
        checkNoPermForpermExceptInhaleExhale(p.e, true)
      })
      permBan = None
      f.body.map(_.e.inner).foreach(check(_, f.typ.resultType)) //result in the function body gets the error message somewhere else
      resultAllowed = false
      curFunction = null
    }
  }

  def checkDeclaration(p: PPredicate): Unit = {
    checkMember(p) {


      p.formalArgs foreach (a => check(a.typ))
    }
  }

  def checkBody(p: PPredicate): Unit = {
    checkMember(p) {
      p.body.foreach(b => {
        check(b.e.inner, Impure)
        checkNoMagicWands(b.e.inner)
      })
    }
  }

  def check(f: PFields): Unit = {
    checkMember(f) {
      f.fields.toSeq foreach (fd => {
        fd.decl = Some(f)
        check(fd.typ)
      })
    }
  }

  def checkFunctions(d: PDomain): Unit = {
    checkMember(d) {
      d.funcs foreach check
    }
  }

  def checkAxioms(d: PDomain): Unit = {
    checkMember(d) {
      d.axioms foreach check
    }
  }

  def check(a: PAxiom): Unit = {
    checkMember(a) {
      check(a.exp.e.inner, Bool)
    }
  }

  def check(f: PDomainFunction): Unit = {
    check(f.typ)
    f.formalArgs foreach (a => check(a.typ))
    // This should probably be reported the name analyser instead
    val idndefs = f.args.inner.toSeq.flatMap(_.name)
    val duplicates = idndefs.groupBy(_.name).collect { case (_, v) if v.length > 1 => v }
    duplicates.foreach(d => messages ++= FastMessaging.message(d.head, s"duplicate argument name `${d.last.name}`"))
  }

  def check(stmt: PStmt): Unit = {
    stmt match {
      case PAnnotatedStmt(_, s) =>
        check(s)
      case s@PSeqn(ss) =>
        checkMember(s) {
          ss.inner.toSeq foreach check
        }
      case PFold(_, e) =>
        acceptNonAbstractPredicateAccess(e, "abstract predicates cannot be folded")
        check(e, Predicate)
      case PUnfold(_, e) =>
        acceptNonAbstractPredicateAccess(e, "abstract predicates cannot be unfolded")
        check(e, Predicate)
      case PPackageWand(_, e, proofScript) =>
        check(e, Wand)
        checkMagicWand(e)
        proofScript foreach check
      case PApplyWand(_, e) =>
        check(e, Wand)
        checkMagicWand(e)
      case PExhale(_, e) =>
        check(e, Impure)
      case PAssert(_, e) =>
        check(e, Impure)
      case PInhale(_, e) =>
        check(e, Impure)
      case PAssume(_, e) =>
        check(e, Impure)
      case assign: PAssign =>
        checkAssign(assign)
      case PLabel(_, _, invs) =>
        invs.toSeq foreach (i => check(i.e, Impure))
      case PGoto(_, _) =>
      case PIf(_, cond, thn, els) =>
        check(cond.inner, Bool)
        check(thn)
        els foreach check
      case PElse(_, els) =>
        check(els)
      case PWhile(_, cond, invs, body) =>
        check(cond.inner, Bool)
        invs.toSeq foreach (inv => {
          check(inv.e, Impure)
          checkNoPermForpermExceptInhaleExhale(inv.e)
        })
        check(body)
      case v: PVars =>
        v.vars.toSeq foreach (v => check(v.typ))
        v.assign foreach checkAssign
      case _: PDefine =>
        /* Should have been removed right after parsing */
        sys.error(s"Unexpected node $stmt found")
      case PQuasihavoc(_, lhs, e) =>
        checkHavoc(stmt, lhs.map(_._1), e)
      case havoc@PQuasihavocall(_, vars, _, lhs, e) =>
        vars.toSeq foreach (v => check(v.typ))
        // update the curMember, which contains quantified variable information
        val oldCurMember = curMember
        curMember = havoc
        // Actually type check the havoc
        checkHavoc(stmt, lhs.map(_._1), e)
        // restore the previous curMember
        curMember = oldCurMember

      case t: PExtender => t.typecheck(this, names).getOrElse(Nil) foreach (message =>
        messages ++= FastMessaging.message(t, message))
      case _: PSkip =>
    }
  }

  def checkAssign(stmt: PAssign): Unit = {
    // Check targets
    stmt.targets.toSeq foreach {
      case idnuse@PIdnUseExp(idnref) =>
        idnref.assignUse = true
        if (idnref.decls.nonEmpty) {
          idnref.filterDecls(_.isInstanceOf[PAssignableVarDecl])
          if (idnref.decl.isDefined)
            check(idnuse, idnref.decl.get.typ)
          else if (idnref.decls.isEmpty)
            messages ++= FastMessaging.message(idnuse, s"expected an assignable identifier `${idnref.name}` as lhs")
          else
            messages ++= FastMessaging.message(idnuse, s"ambiguous identifier `${idnref.name}`, expected single parameter or local variable")
        } else
          messages ++= FastMessaging.message(idnuse, s"undeclared identifier `${idnref.name}`, expected parameter or local variable")
      case fa@PFieldAccess(rcv, _, field) =>
        checkTopTyped(rcv, None)
        getDatatypeByName(rcv.typ) match {
          case Some(dt) => {
            getInstantiatedFieldType(rcv.typ, field.name) match {
              case Some(fieldType) => check(fa, fieldType)
              case None => messages ++= FastMessaging.message(fa, s"datatype `${dt.idndef.name}` does not have field ${field.name}")
            }

          }
          case None => {
            field.assignUse = true
            if (field.decl.isDefined)
              check(fa, field.decl.get.typ)
            else if (field.decls.length > 1)
              messages ++= FastMessaging.message(field, s"ambiguous field `${field.name}`")
            else
              messages ++= FastMessaging.message(field, s"123 undeclared field `${field.name}`")
          }
        }
      case call: PCall => sys.error(s"Unexpected node $call found")
    }

    def mergeUnificationResults(u1: Map[String, PType], u2: Map[String, PType]): Option[Map[String, PType]] = {
      // merging the two instantiation maps by checking the overlapping assignments for equality
      // and then merging the kv pairs of both maps
      u2.keys.foldLeft[Option[Map[String, PType]]](Some(u1))((acc, k) =>
        acc match {
          case Some(m) => m.get(k) match {
            case Some(typ) =>
              if (u2(k).equals(typ)) {
                acc
              } else {
                None
              }
            case None => {
              val kv: (String, PType) = (k, u2(k))
              val extended: Map[String, PType] = m + kv
              Some(extended)
            }
          }
          case None => None
        })
    }

    def findUnificationForPair(call: PNode, arg: PType, value: PType): Option[Map[String, PType]] = {
      (arg, value) match {
        case (PUnknown(), PUnknown()) => Some(Map())
        case (PBoolImpureType(), PBoolImpureType()) => Some(Map())
        case (PBoolWandType(), PBoolWandType()) => Some(Map())
        case (PBoolPredicateType(), PBoolPredicateType()) => Some(Map())
        case (PFunctionType(a1, r1), PFunctionType(a2, r2)) => {
          val mappedArgs1 = a1 ++ Seq(r1)
          val mappedArgs2 = a2 ++ Seq(r2)
          if (mappedArgs1.length == mappedArgs2.length) {
            mappedArgs1.zip(mappedArgs2)
              .map(v => findUnificationForPair(call, v._1, v._2))
              .foldLeft[Option[Map[String, PType]]](Some(Map()))((acc, v) => (acc, v) match {
                case (Some(m1), Some(m2)) => mergeUnificationResults(m1, m2)
                case _ => None
              })
          }
          else {
            None
          }
        }
        case (PMacroType(u1), PMacroType(u2)) => if (u1.idnref.equals(u2.idnref)) {
          Some(Map())
        } else {
          None
        }
        case (PMapType(_, t1), PMapType(_, t2)) =>
          val res1 = findUnificationForPair(call, t1.inner.first, t2.inner.first)
          val res2 = findUnificationForPair(call, t1.inner.second, t2.inner.second)
          (res1, res2) match {
            case (Some(v1), Some(v2)) => mergeUnificationResults(v1, v2)
            case _ => None
          }
        case (PMultisetType(_, elem1), PMultisetType(_, elem2)) => findUnificationForPair(call, elem1.inner, elem2.inner)
        case (PPrimitiv(n1), PPrimitiv(n2)) => if (n1.rs.equals(n2.rs)) {
          Some(Map())
        } else {
          None
        }
        case (PSeqType(_, elem1), PSeqType(_, elem2)) => findUnificationForPair(call, elem1.inner, elem2.inner)
        case (PSetType(_, elem1), PSetType(_, elem2)) => findUnificationForPair(call, elem1.inner, elem2.inner)
        // TODO: add case for generic parameter and every other type
        case (d1@PDomainType(dom1, _), d2) if d1.kind == PDomainTypeKinds.TypeVar =>
          // TODO: set the substitution
          Some(Seq((dom1.name, d2)).toMap)
        case (d1@PDomainType(dom1, args1), d2@PDomainType(dom2, args2)) =>
          val mappedArgs1 = args1.map(_.inner.toSeq).getOrElse(Nil)
          val mappedArgs2 = args2.map(_.inner.toSeq).getOrElse(Nil)
          if (d1.kind == d2.kind && dom1.name.equals(dom2.name) && mappedArgs1.length == mappedArgs2.length) {
            mappedArgs1.zip(mappedArgs2)
              .map(v => findUnificationForPair(call, v._1, v._2))
              .foldLeft[Option[Map[String, PType]]](Some(Map()))((acc, v) => (acc, v) match {
                case (Some(m1), Some(m2)) => mergeUnificationResults(m1, m2)
                case _ => None
              })
          }
          else {
            None
          }
        case _ => {
          messages ++= FastMessaging.message(call, s"failed unification of `${arg}` and `${value}`")
          None
        }
      }
    }

    def findUnificationForArgs(call: PNode, argPairs: Seq[(PType, PType)]): Option[Map[String, PType]] = {
      val result = argPairs.map(p => (p, findUnificationForPair(call, p._1, p._2)))
        .foldLeft((false, Map[String, PType]()))((res, rr) => {
          val m2 = rr._2
          val failed = res._1
          val currentMapping = res._2
          m2 match {
            case Some(value) =>
              value.keys.foldLeft((failed, currentMapping))((acc, k) => {
                acc._2.get(k) match {
                  case Some(typ) =>
                    if (value(k).equals(typ)) {
                      (acc._1, acc._2)
                    }
                    else {
                      messages ++= FastMessaging.message(call, s"incompatible generic parameter instantiations `$typ` and `${value(k)}` (originating from: `${rr._1._1}` and `${rr._1._2}`)")
                      (true, acc._2)
                    }
                  case None => {
                    val kv: (String, PType) = (k, value(k))
                    val extended: Map[String, PType] = acc._2 + kv
                    (acc._1, extended)
                  }
                }
              })
            case None => {
              (true, currentMapping)
            }
          }
        })
      if (result._1) {
        None
      }
      else {
        Some(result._2)
      }
    }

    // Check rhs
    stmt match {
      case PAssign(targets, _, c@PCall(func, _, _)) if targets.length != 1 || func.decls.forall(!_.isInstanceOf[PAnyFunction]) =>
        if (func.filterDecls(_.isInstanceOf[PMethod]))
          messages ++= FastMessaging.message(func, s"undeclared call `${func.name}`, expected function or method")
        else if (func.filterDecls(_.asInstanceOf[PMethod].formalArgs.length == c.args.length))
          messages ++= FastMessaging.message(c, s"wrong number of arguments")
        else if (func.filterDecls(_.asInstanceOf[PMethod].formalReturns.length == targets.length))
          messages ++= FastMessaging.message(stmt, s"wrong number of targets")
        else if (func.decl.isEmpty)
          messages ++= FastMessaging.message(stmt, "ambiguous method call")
        else {
          val m = func.decl.get.asInstanceOf[PMethod]
          val formalTargets = m.formalReturns
          val formalArgs = m.formalArgs
          println(s"instantiation: ${c.args} -> ${formalArgs}")
          c.args.foreach(a => {
            checkTopTyped(a, None)
          })
          formalArgs.foreach(fa => check(fa.typ))
          val unificationResult = findUnificationForArgs(c, formalArgs.map(f => f.typ) zip c.args.map(e => e.typ))
          unificationResult match {
            case Some(r) => {
              val ts = PTypeSubstitution(r)
              for ((formal, actual) <- (formalTargets zip targets.toSeq)) {
                check(actual, formal.typ.substitute(ts))
              }
            }
            case None =>
              messages ++= FastMessaging.message(c, s"unable to unify arguments of method call `${c.pretty}`")
          }
          // TODO CFG: record the instantiation of the method
        }
      case PAssign(targets, _, PNewExp(_, fields)) if targets.length == 1 =>
        check(targets.head, Ref)
        fields.inner match {
          case Right(fields) => fields.toSeq foreach (f => {
            if (f.decls.isEmpty)
              messages ++= FastMessaging.message(f, s"456 undeclared field `${f.name}`")
            else if (f.decls.length > 1)
              messages ++= FastMessaging.message(f, s"ambiguous field `${f.name}`")
          })
          case Left(_) =>
        }
      case PAssign(targets, _, rhs) if targets.length == 1 => check(rhs, targets.head.typ)
      // Anything after this has to satisfy `targets.length != 1 && !rhs.isInstanceOf[PCall]`:
      // Parsed `expr`
      case _ if stmt.op.isEmpty => messages ++= FastMessaging.message(stmt, "invalid expression in statement position, only method calls with no returns are allowed in a statement position")
      // Parsed `:= expr`
      case _ if stmt.targets.isEmpty => messages ++= FastMessaging.message(stmt, "expected a target when assigning an expression")
      case _ => messages ++= FastMessaging.message(stmt, "expected a method call when assigning to multiple targets")
    }
  }

  def checkHavoc(stmt: PStmt, lhs: Option[PExp], e: PExp): Unit = {
    // If there is a condition, make sure that it is a Bool
    if (lhs.nonEmpty) {
      check(lhs.get, Bool)
    }
    // Make sure that the rhs is a resource
    val havocError = "Havoc statement must take a field access, predicate, or wand"
    e match {
      case _: PFieldAccess => checkTopTyped(e, None)
      case pc: PCall =>
        check(e, Impure)
        // make sure that this is in fact a predicate
        if (!pc.isPredicate) {
          messages ++= FastMessaging.message(stmt, havocError)
        }
      case _: PMagicWandExp => check(e, Impure)
      case _ => messages ++= FastMessaging.message(stmt, havocError)
    }
  }

  def acceptNonAbstractPredicateAccess(exp: PExp, messageIfAbstractPredicate: String): Unit = {
    val call = exp match {
      case acc: PAccPred if acc.loc.isInstanceOf[PCall] => acc.loc.asInstanceOf[PCall]
      case call: PCall => call

      case _ =>
        messages ++= FastMessaging.message(exp, "expected predicate access")
        return
    }
    if (call.idnref.decls.isEmpty)
      messages ++= FastMessaging.message(call.idnref, s"undeclared predicate `${call.idnref.name}`")
    else if (call.idnref.filterDecls(_.isInstanceOf[PPredicate]))
      messages ++= FastMessaging.message(call.idnref, s"expected predicate access `${call.idnref.name}")
    else if (call.idnref.decl.isEmpty)
      messages ++= FastMessaging.message(call.idnref, s"ambiguous predicate access `${call.idnref.name}")
    else if (call.idnref.decl.get.asInstanceOf[PPredicate].body.isEmpty)
      messages ++= FastMessaging.message(call.idnref, messageIfAbstractPredicate)
  }

  def checkMagicWand(e: PExp): Unit = e match {
    case PBinExp(_, PReserved(PSymOp.Wand), _) =>
    case _ =>
      messages ++= FastMessaging.message(e, "expected magic wand")
  }

  def checkNoPermForpermExceptInhaleExhale(e: PExp, skipForPerm: Boolean = false): Unit = {
    val errors = e.shallowCollect({
      case p: PCurPerm => Some(p)
      case p: PForPerm if !skipForPerm => Some(p)
      case _: PInhaleExhaleExp => None
    }).flatten
    errors.foreach(e => {
      messages ++= FastMessaging.message(e, "preconditions, postconditions and invariants may only contain `perm` and `forperm` expressions inside of an inhale-exhale")
    })
  }

  def checkNoMagicWands(e: PExp): Unit =
    e.shallowCollect({ case p: PMagicWandExp => p }).foreach(e => {
      messages ++= FastMessaging.message(e, "magic wands are not supported in function preconditions or predicates")
    })

  def getDatatypeByName(name: String): Option[PDatatype] = {
    this.program.datatypes
      .find(_.idndef.name.equals(name))
  }

  def getDatatypeByName(typ: PType): Option[PDatatype] = {
    typ match {
      case PDomainType(dom, args) => getDatatypeByName(dom.name)
      case _ => None
    }
  }


  def getInstantiatedFieldType(t: PType, fieldName: String): Option[PType] = {
    t match {
      case PDomainType(dom, args) => {
        getDatatypeByName(dom.name) match {
          case Some(d) => {
            d.getFieldDeclTypeByName(fieldName) match {
              case Some(fieldTyp) => {
                // TODO: substitute args for parameters
                val elems: Seq[(String, PType)] = d.typVarsSeq.zip(args.map(v => v.inner.toSeq).getOrElse(Nil))
                  .map(f => (f._1.idndef.name, f._2))
                val ts: PTypeSubstitution = PTypeSubstitution(elems.toMap)
                Some(fieldTyp.substitute(ts))

              }
              case None => {
                println(s"No field in the datatype ${fieldName}")
                None
              }
            }
          }
          case None => None
        }
      }
      case _ => None
    }
  }

  def check(typ: PType): Unit = {
    typ match {
      case PPrimitiv(_) =>
      /* Nothing to type check (or resolve) */
      case dt@PDomainType(_, _) if dt.isResolved =>
      /* Already resolved, nothing left to do */
      case dt@PDomainType(domain, args) =>
        assert(!dt.isResolved, "Only yet-unresolved domain types should be type-checked and resolved")

        args foreach (_.inner.toSeq foreach check)

        val datatype = getDatatypeByName(dt.domain.name)

        datatype match {
          case Some(d) => {
            val expectedNumArgs = d.typVars.map(v => v.inner.toSeq).getOrElse(Nil).length
            val actualNumArgs = dt.typeArguments.length
            if (expectedNumArgs != actualNumArgs)
              messages ++= FastMessaging.message(dt, s"diverging number of type parameters for type `${domain.name}`, expected $expectedNumArgs got $actualNumArgs")
            else
              dt.kind = PDomainTypeKinds.Datatype
            // TODO CFG: ensure number of parameters matches
          }
          case None => {
            dt.kind = PDomainTypeKinds.Undeclared

            if (domain.decls.isEmpty) {
              if (args.isDefined)
                messages ++= FastMessaging.message(dt, s"undeclared type `${domain.name}`, expected domain")
              else
                messages ++= FastMessaging.message(dt, s"undeclared type `${domain.name}`")
            } else {
              if (args.isDefined) {
                if (domain.filterDecls(d => d.isInstanceOf[PDomain] && d.asInstanceOf[PDomain].typVars.isDefined && d.asInstanceOf[PDomain].typVars.get.inner.length == args.get.inner.length))
                  messages ++= FastMessaging.message(dt, s"undeclared type `${domain.name}`, expected domain with ${args.get.inner.length} type argument${if (args.get.inner.length == 1) "" else "s"}")
              } else {
                if (domain.filterDecls(d => !d.isInstanceOf[PDomain] || (d.isInstanceOf[PDomain] && d.asInstanceOf[PDomain].typVars.isEmpty)))
                  messages ++= FastMessaging.message(dt, s"undeclared type `${domain.name}`, found domain with type arguments")
              }

              if (domain.decl.isEmpty) {
                if (domain.decls.length > 1)
                  messages ++= FastMessaging.message(dt, s"ambiguous type `${domain.name}`")
              } else domain.decl.get match {
                case PDomain(_, _, _, typVars, _, _) =>
                  // Should never fail, checked above with `filterDecls`
                  ensure(args.map(_.inner.length) == typVars.map(_.inner.length), typ, "wrong number of type arguments")
                  dt.kind = PDomainTypeKinds.Domain
                case PTypeVarDecl(_) =>
                  dt.kind = PDomainTypeKinds.TypeVar
              }
            }
          }
        }

      case PSeqType(_, elemType) =>
        check(elemType.inner)
      case PSetType(_, elemType) =>
        check(elemType.inner)
      case PMultisetType(_, elemType) =>
        check(elemType.inner)
      case m: PMapType =>
        check(m.keyType)
        check(m.valueType)
      case PFunctionType(argTypes, resultType) =>
        argTypes map check
        check(resultType)
      case t: PExtender =>
        t.typecheck(this, names).getOrElse(Nil) foreach (message =>
          messages ++= FastMessaging.message(t, message))
      case _: PInternalType =>
        sys.error("unexpected use of internal typ")
    }
  }

  /*
   * Parameters:
   * rlts: local substitutions, refreshed
   * argData: a sequence of tuples, one per op arguments, where
   *          _1 is the type of the argument expression
   *          _2 is the fresh local argument type
   *          _3 is the set of substitutions of the argument expression
   *          _4 is the argument expression itself (used to extract a precise position)
   * Returns:
   * Either a new type substitution (right case) or, in case of failure (left) a triple containing
   *          _1 the expected type
   *          _2 the found type
   *          _3 the argument that caused the failure
   */
  def unifySequenceWithSubstitutions(rlts: Seq[PTypeSubstitution],
                                     argData: scala.collection.immutable.Seq[(PType, PType, Seq[PTypeSubstitution], PExp)])
  : Either[(PType, PType, PExp), Seq[PTypeSubstitution]] = {
    // Merge all the substitutions of all arguments
    var pss = rlts.map(ts => PTypeSubstitutionInternal(ts.m))
    for (tri <- argData) {
      val current = (for (ps <- pss; aps <- tri._3)
        yield ps.compose(aps))
      val allBad = current.forall(e => e.isLeft)
      if (allBad) {
        val badMatch = current.find(e => e.isLeft)
        val badTypes = badMatch.get.swap.toOption.get
        return Left(badTypes._1, badTypes._2, tri._4)
      }
      pss = current.flatMap(_.toOption)
    }

    // Add in the signature -> argument type substitutions
    for (tri <- argData) {
      val current = (for (ps <- pss)
        yield ps.add(tri._1, tri._2))
      val allBad = current.forall(e => e.isLeft)
      if (allBad) {
        val badMatch = current.find(e => e.isLeft)
        val badTypes = badMatch.get.swap.toOption.get
        return Left(badTypes._1, badTypes._2, tri._4)
      }
      pss = current.flatMap(_.toOption)
    }
    Right(pss.map(_.collapse))
  }

  def ground(exp: PExp, pts: PTypeSubstitution): PTypeSubstitution = {
    pts.m.flatMap(kv => kv._2.freeTypeVariables &~ pts.m.keySet).foldLeft(pts)((ts, fv) => {
      var chosenType: PType = PTypeSubstitution.defaultType
      curMember.getAncestor[PDomain] match {
        case Some(domain: PDomain) =>
          // If we are inside the domain that defines the type variable, then we choose the type variable itself
          // as the default.
          // The name pf domain function application type variables has the form
          // domainName + PTypeVar.domainNameSep + typeVarName + PTypeVar.sep + index
          if (fv.startsWith(domain.idndef.name + PTypeVar.domainNameSep)) {
            var tvName = fv.substring(domain.idndef.name.length + 1)
            if (tvName.contains(PTypeVar.sep)) {
              tvName = tvName.substring(0, tvName.indexOf(PTypeVar.sep))
              if (domain.typVarsSeq.exists(tv => tv.idndef.name == tvName)) {
                // The type variable refers to an actual type variable of the current domain.
                chosenType = PTypeVar(tvName)
              }
            }
          }
        case _ =>
      }
      if (chosenType == PTypeSubstitution.defaultType) {
        messages ++= FastMessaging.message(exp,
          s"unconstrained type parameter, substituting default type ${PTypeSubstitution.defaultType}", error = false)
      }
      ts.add(PTypeVar(fv), chosenType).toOption.get
    })
  }

  def selectAndGroundTypeSubstitution(exp: PExp, etss: collection.Seq[PTypeSubstitution]): PTypeSubstitution = {
    require(etss.nonEmpty)
    ground(exp, etss.head)
  }

  def typeError(exp: PExp) = {
    messages ++= FastMessaging.message(exp, s"type error")
  }

  def check(exp: PExp, expected: PType) = exp match {
    case t: PExtender => t.typecheck(this, names, expected).getOrElse(Nil) foreach (message =>
      messages ++= FastMessaging.message(t, message))

    case _ => checkTopTyped(exp, Some(expected))
  }

  def checkTopTyped(exp: PExp, oexpected: Option[PType]): Unit = {
    checkInternal(exp)
    if (exp.typ.isValidOrUndeclared && exp.typeSubstitutions.nonEmpty) {
      val etss = oexpected match {
        case Some(expected) if expected.isValidOrUndeclared => exp.typeSubstitutions.flatMap(_.add(exp.typ, expected).toOption)
        case _ => exp.typeSubstitutions
      }
      var error = true
      if (etss.nonEmpty) {
        val ts = selectAndGroundTypeSubstitution(exp, etss)
        exp.forceSubstitution(ts)
        error = oexpected.isDefined && !isSubtype(exp.typ, oexpected.get)
      }
      // special logic to resolve ambiguity of null literal and expected DT type
      if (oexpected.isDefined && exp.isInstanceOf[PNullLit] && getDatatypeByName(oexpected.get).isDefined) {
        exp.typ = oexpected.get
        error = false
      }

      if (error) oexpected match {
        case Some(expected) =>
          val reportedActual = if (exp.typ.isGround) {
            exp.typ
          } else {
            exp.typ.substitute(selectAndGroundTypeSubstitution(exp, exp.typeSubstitutions))
          }
          messages ++= FastMessaging.message(exp, s"123 found incompatible type `${reportedActual.pretty}`, expected `${expected.toString()}`")
        case None =>
          typeError(exp)
      }
    }
  }

  def checkInternal(exp: PExp): Unit = {
    /**
     * Set the type of 'exp', and check that the actual type is allowed by one of the expected types.
     */
    def setType(actual: PType): Unit = {
      exp.typ = actual
    }

    /**
     * Issue an error for the node at 'n'. Also sets an error type for 'exp' to suppress
     * further warnings.
     *
     * TODO: Similar to Consistency.recordIfNot. Combine!
     */
    def issueError(n: PNode, m: String): Unit = {
      messages ++= FastMessaging.message(n, m)
      setErrorType() // suppress further warnings
    }

    /**
     * Sets an error type for 'exp' to suppress further warnings.
     */
    def setErrorType(): Unit = {
      setType(PUnknown())
    }

    /**
     * Checks if a given expression contains a permission amount that is more specific than stating whether an amount
     * is zero or positive.
     */
    def hasSpecificPermAmounts(e: PExp): Boolean = e match {
      case PCondExp(_, _, thn, _, els) => hasSpecificPermAmounts(thn) || hasSpecificPermAmounts(els)
      case _: PWildcard => false
      case _: PNoPerm => false
      case _ => true
    }

    def getFreshTypeSubstitution(tvs: Seq[PDomainType]): PTypeRenaming =
      PTypeVar.freshTypeSubstitutionPTVs(tvs)


    //Checks that a substitution is fully reduced (idempotent)
    def refreshWith(ts: PTypeSubstitution, rts: PTypeRenaming): PTypeSubstitution = {
      require(ts.isFullyReduced)
      require(rts.isFullyReduced)
      //      require(rts.values.forall { case pdt: PDomainType if pdt.isTypeVar => true case _ => false })
      new PTypeSubstitution(ts map (kv => rts.rename(kv._1) -> kv._2.substitute(rts)))
    }

    var extraReturnTypeConstraint: Option[PType] = None

    exp match {
      /*
        An extra hook for extending the TypeChecker in case of expressions as this portion of the TypeChecker for expressions is
        accessible only when an expression is used inside another expression(an extremely frequent occurrence).
        The main aim is to give the plugin developer more options as to whether type checking with an expected return type
        is preferred or a simplistic approach.
       */

      case m: PMakeExp => {
        // TODO CFG: fix this
        setType(m.constTyp)
      }

      case t: PExtender => t.typecheck(this, names).getOrElse(Nil) foreach (message =>
        messages ++= FastMessaging.message(t, message))
      case PAnnotatedExp(_, e) =>
        checkInternal(e)
        setType(e.typ)
      case psl: PSimpleLiteral =>
        psl match {
          case r@PResultLit(_) =>
            if (resultAllowed)
              setType(curFunction.typ.resultType)
            else
              issueError(r, "`result` can only be used in function postconditions")
          case _ =>
        }

      case poa: POpApp =>
        var isSpecialLookup: Boolean = false
        var resultingFieldType: PType = null

        if (poa.typeSubstitutions.isEmpty) {
          poa.args.foreach(checkInternal)
          var nestedTypeError = !poa.args.forall(a => a.typ.isValidOrUndeclared)
          if (!nestedTypeError) {
            // Check purity of arguments
            poa.requirePure.foreach(a => if (!a.typ.isPure) issueError(a, "argument is not pure"))

            poa match {
              case pfa@PCall(func, _, explicitType) =>
                explicitType match {
                  case Some((_, t)) =>
                    check(t)
                    if (!t.isValidOrUndeclared) nestedTypeError = true
                  case None =>
                }

                // Resolve the function name to a function declaration
                if (func.decls.nonEmpty) {
                  func.filterDecls(_.isInstanceOf[PAnyFunction])
                  if (func.decls.isEmpty)
                    issueError(func, "expected function or predicate")
                  else if (func.decls.length > 1) {
                    issueError(func, "ambiguous function or predicate")
                  }
                }
                if (func.decls.isEmpty)
                  issueError(func, s"undeclared call `${func.name}`, expected function or predicate")
                else if (func.filterDecls(_.isInstanceOf[PAnyFunction]))
                  issueError(func, s"invalid method call `${func.name}` in expression position, expected function or predicate")
                else if (func.decl.isEmpty)
                  issueError(func, s"ambiguous call `${func.name}`")
                else {
                  val fd = func.decl.get.asInstanceOf[PAnyFunction]
                  ensure(fd.formalArgs.length == pfa.args.length, pfa, "wrong number of arguments")
                  if (!nestedTypeError) {
                    extraReturnTypeConstraint = explicitType.map(_._2)
                    fd match {
                      case pfn: PFunction =>
                        checkMember(fd) {
                          check(fd.typ)
                          fd.formalArgs foreach (a => check(a.typ))
                        }
                        if (pfa.isDescendant[PAxiom] && pfn.pres.toSeq.exists(pre => pre.k.rs == Requires)) {
                          // A domain axiom, which must always be well-defined, is calling a function that has at least
                          // one real precondition (i.e., not just a requires clause or something similar that's
                          // temporarily represented as a precondition), which means that the call may not always be
                          // well-defined. This is not allowed.
                          issueError(func, s"Cannot use function ${func.name}, which has preconditions, inside axiom")
                        }

                      case pdf: PDomainFunction =>
                        val domain = pdf.domain
                        val typVars = domain.typVarsSeq
                        val fdtv = PTypeVar.freshTypeSubstitution((typVars map (tv => tv.idndef.name)).distinct, Some(domain.idndef.name)) //fresh domain type variables
                        pfa.domainTypeRenaming = Some(fdtv)
                        pfa._extraLocalTypeVariables = (typVars map (tv => PTypeVar(tv.idndef.name))).toSet
                      case _: PPredicate =>
                        if (explicitType.isDefined)
                          issueError(pfa, "predicate call cannot have an explicit type")
                    }
                  }
                }

              case pu: PUnfolding =>
                acceptNonAbstractPredicateAccess(pu.acc, "abstract predicates cannot be unfolded")

              case PApplying(_, wand, _, _) =>
                checkMagicWand(wand)

              // We checked that the `rcv` is valid above with `poa.args.foreach(checkInternal)`
              case fa@PFieldAccess(rcv, _, idnref) =>
                getDatatypeByName(rcv.typ) match {
                  case Some(dt) => {
                    getInstantiatedFieldType(rcv.typ, idnref.name) match {
                      case Some(fieldType) => {
                        fa.typ = fieldType
                        isSpecialLookup = true
                        resultingFieldType = fieldType
                      }
                      case None => issueError(idnref, s"datatype `${dt.idndef.name}` has no field  ${idnref}")
                    }

                  }
                  case None => {
                    if (idnref.decls.isEmpty)
                      issueError(idnref, s"789 undeclared field `${idnref.name}`   ${rcv.typ}")
                    else if (idnref.decl.isEmpty)
                      issueError(idnref, s"ambiguous field `${idnref.name}`    ${rcv.typ}")
                  }
                }


              case acc: PAccPred =>
                acc.loc match {
                  case _: PFieldAccess =>
                  case pc: PCall if pc.isPredicate => {
                    println(s"Call: ${pc}")
                  }
                  case pc: PPredCall if pc.isPredicate => {
                    println(s"PredCall: ${pc}")
                    println(s"tv -> ${pc.params.map(v => v.inner.toSeq).getOrElse(Nil)}")
                    println(s"args -> ${pc.callArgs.inner.toSeq}")
                  }
                  case loc =>
                    println(acc.loc.pretty)
                    issueError(loc, "specified location is not a field nor a predicate")
                }
                acc.permExp match {
                  case Some(pe) if curMember.isInstanceOf[PFunction] && warnAboutFunctionPermAmounts && hasSpecificPermAmounts(pe) =>
                    val msg = "Function contains specific permission amount that will be treated like wildcard if it is positive and none otherwise."
                    messages ++= FastMessaging.message(pe, msg, error = false)
                  case _ =>
                }

              case pecl: PEmptyCollectionLiteral if !pecl.pElementType.isValidOrUndeclared =>
                check(pecl.pElementType)

              case pem: PEmptyMap if !pem.pKeyType.isValidOrUndeclared || !pem.pValueType.isValidOrUndeclared =>
                if (!pem.pKeyType.isValidOrUndeclared)
                  check(pem.pKeyType)
                if (!pem.pValueType.isValidOrUndeclared)
                  check(pem.pValueType)

              case _: PCurPerm =>
                if (permBan.isDefined)
                  issueError(poa, s"${permBan.get} are not allowed to contain `perm` expressions")

              case _ =>
            }
          }


          if ((poa.signatures.nonEmpty || isSpecialLookup) && poa.args.forall(_.typeSubstitutions.nonEmpty) && !nestedTypeError) {
            val ltr = getFreshTypeSubstitution(poa.localScope.toList) //local type renaming - fresh versions
            val rlts = (if (isSpecialLookup)
              poa match {
                case PFieldAccess(rcv, _, field) => {
                  val signatureList = List(
                    Map(POpApp.pArgS(0) -> rcv.typ, POpApp.pResS -> resultingFieldType)
                  )
                  signatureList map (ts => refreshWith(ts, ltr))
                }
              }
            else poa.signatures map (ts => refreshWith(ts, ltr))) //local substitutions refreshed)
            val rrt: PDomainType = POpApp.pRes.substitute(ltr).asInstanceOf[PDomainType] // return type (which is a dummy type variable) replaced with fresh type

            def isTypeVar(t: PType): Boolean = {
              t match {
                case d: PDomainType => d.kind == PDomainTypeKinds.TypeVar
                case _ => false
              }
            }

            poa match {
              case exp: PBinExp => {
                // special case for comparing a datatype to null which is ambiguous with the ref type
                val leftIsDT = getDatatypeByName(exp.left.typ).isDefined || isTypeVar(exp.left.typ)
                val rightIsDT = getDatatypeByName(exp.right.typ).isDefined || isTypeVar(exp.right.typ)
                println(s"LR TYP: ${exp.left.typ}    ${exp.right.typ}")
                if (exp.op.rs == EqEq || exp.op.rs == Ne) {
                  println(s"checking if left right is null: ${poa.pretty}")
                  if (leftIsDT && exp.right.isInstanceOf[PNullLit]) {
                    println("LEFT IS DT")
                    exp.right.typ = exp.left.typ
                  }

                  if (rightIsDT && exp.left.isInstanceOf[PNullLit]) {
                    println("RIGHT IS DT")
                    exp.left.typ = exp.right.typ
                  }
                }
              }
              case _ =>
            }
            // Continue only if there was no error in the arguments
            if (rlts.nonEmpty && poa.args.forall(_.typeSubstitutions.nonEmpty) && !nestedTypeError) {
              val flat = poa.args.indices map (i => POpApp.pArg(i).substitute(ltr)) //fresh local argument types
              // the quadruples below are: (fresh argument type, argument type as used in domain of substitutions, substitutions, expression)
              val argData = flat.indices.map(i => (poa.args(i).typ, flat(i), poa.args(i).typeSubsDistinct.toSeq, poa.args(i))) ++
                (extraReturnTypeConstraint match {
                  case None => Nil
                  case Some(t) => Seq((t, rrt, List(PTypeSubstitution.id), poa))
                })
              val unifiedSequence = unifySequenceWithSubstitutions(rlts, argData)
              if (unifiedSequence.isLeft && poa.typeSubstitutions.isEmpty) {
                val problem = unifiedSequence.left.toOption.get
                messages ++= FastMessaging.message(problem._3, s"456 found incompatible type `${problem._1.pretty}`, expected `${problem._2.pretty}   ${poa.pretty}`")
              } else {
                poa.typeSubstitutions ++= unifiedSequence.toOption.get
                val ts = poa.typeSubsDistinct
                poa.typ = if (ts.size == 1) rrt.substitute(ts.head) else rrt
              }
            } else {
              poa.typeSubstitutions.clear()
              // Try to get a correct type even though the
              val ts = rlts.map(rrt.substitute(_)).distinct
              if (ts.size == 1) {
                poa.typeSubstitutions += rlts.find(_.contains(rrt)).get
                poa.typ = ts.head
              } else {
                poa.typ = PUnknown()
              }
            }
          }
        }

      case piu@PIdnUseExp(idnref) =>
        if (idnref.decls.isEmpty)
          issueError(piu, s"undeclared identifier `${idnref.name}`")
        else if (idnref.decl.isEmpty)
          issueError(piu, s"ambiguous identifier `${idnref.name}`")
        else {
          piu.typ = idnref.decl.get.typ
        }

      case piu: PVersionedIdnUseExp =>
        if (piu.decls.isEmpty)
          issueError(piu, s"undeclared identifier `${piu.name}`")
        else if (piu.decl.isEmpty)
          issueError(piu, s"ambiguous identifier `${piu.name}`")
        else
          piu.typ = piu.decl.get.typ

      case pl@PLet(_, _, _, e, _, ns) =>
        val oldCurMember = curMember
        curMember = pl
        checkInternal(e.inner)
        checkInternal(ns.body)
        pl.typ = ns.body.typ
        curMember = oldCurMember

      case pq: PForPerm =>
        if (permBan.isDefined)
          issueError(pq, s"${permBan.get} are not allowed to contain `forperm` expressions")
        val oldCurMember = curMember
        curMember = pq
        pq.boundVars foreach (v => check(v.typ))
        val oldPermBan = permBan
        permBan = Some("forperm quantifier bodies")
        check(pq.body, Bool)
        permBan = oldPermBan
        checkTopTyped(pq.accessRes, None)
        pq.triggers foreach (_.exp.inner.toSeq foreach (tpe => checkTopTyped(tpe, None)))
        pq._typeSubstitutions = pq.body.typeSubstitutions.toList.distinct
        pq.typ = Bool
        curMember = oldCurMember

      case pq: PQuantifier =>
        val oldCurMember = curMember
        curMember = pq
        pq.boundVars foreach (v => check(v.typ))
        val expected = if (pq.isInstanceOf[PForall]) Impure else Bool
        check(pq.body, expected)
        pq.triggers foreach (_.exp.inner.toSeq foreach (tpe => checkTopTyped(tpe, None)))
        pq._typeSubstitutions = pq.body.typeSubstitutions.toList.distinct
        pq.typ = pq.body.typ
        curMember = oldCurMember

      case pne: PNewExp => issueError(pne, s"unexpected use of `new` as an expression")
    }
  }

  def checkExtension(e: PExtender): Unit = e.typecheck(this, names).getOrElse(Nil) foreach (message =>
    messages ++= FastMessaging.message(e, message))

  /**
   * If b is false, report an error for node.
   */
  def ensure(b: Boolean, node: PNode, msg: String): Unit = {
    if (!b) messages ++= FastMessaging.message(node, msg)
  }
}

case class DeclarationMap(
                           decls: mutable.HashMap[String, mutable.Buffer[PDeclaration]] = mutable.HashMap.empty,
                           unique: mutable.HashMap[String, (Boolean, PDeclaration)] = mutable.HashMap.empty,
                           refs: mutable.HashMap[String, mutable.Buffer[PIdnUseName[_]]] = mutable.HashMap.empty,
                           isMember: Boolean,
                           isGlobal: Boolean = false,
                         ) {
  def checkUnique(decl: PDeclaration, canUnique: Boolean): Option[PDeclaration] = {
    val name = decl.idndef.name
    val uniq = unique.get(name)
    val uniqGlobal = uniq.map(u => u._1 && u._2.isInstanceOf[PGlobalUniqueDeclaration]).getOrElse(false)
    val uniqMember = uniqGlobal || uniq.map(u => u._1 && u._2.isInstanceOf[PMemberUniqueDeclaration]).getOrElse(false)
    val uniqScope = uniqMember || uniq.map(u => u._1 && u._2.isInstanceOf[PScopeUniqueDeclaration]).getOrElse(false)
    decl match {
      case _: PGlobalUniqueDeclaration if canUnique => unique.update(name, (canUnique, decl))
      case _: PMemberUniqueDeclaration if !uniqGlobal && canUnique => unique.update(name, (canUnique, decl))
      case _: PScopeUniqueDeclaration if !uniqMember && canUnique => unique.update(name, (canUnique, decl))
      case _ if uniqScope =>
      case _ =>
        // Neither is unique, use last seen
        unique.update(name, (canUnique, decl))
        return None
    }
    uniq.map(_._2)
  }

  def newDecl(decl: PDeclaration) = {
    val name = decl.idndef.name
    // Backward references
    if (decl.isInstanceOf[PBackwardDeclaration])
      refs.get(name).foreach(_.foreach(_.newDecl(decl)))
    // Add to declaration map
    val buf = decls.getOrElseUpdate(name, mutable.Buffer.empty)
    if (decl.isInstanceOf[POverridesDeclaration])
      buf.clear()
    buf += decl
  }

  def merge(map: DeclarationMap): Seq[(PDeclaration, PDeclaration)] = {
    // Add outer decls to inner refs
    map.refs.flatMap(r => decls.get(r._1).map(_ -> r._2)).foreach {
      case (ds, rs) => rs
        .filter(_.decls.forall(!_.isInstanceOf[POverridesDeclaration]))
        .foreach(_.prependDecls(ds.toSeq))
    }
    // Save inner decls and add them to outer refs
    map.decls.values.foreach(_.foreach(d =>
      if (!d.isInstanceOf[PLocalDeclaration] &&
        !(d.isInstanceOf[PMemberDeclaration] && map.isMember) &&
        !(d.isInstanceOf[PGlobalDeclaration] && map.isGlobal)
      ) newDecl(d)
    ))
    // Save inner refs
    map.refs.foreach { case (k, rs) => refs.getOrElseUpdate(k, mutable.Buffer.empty) ++= rs }
    // Propagate inner unique declarations to outer.
    // Cannot simply use `decls` since we could miss an inner local declaration clashing with an outer unique one (or even a `PLocalDeclaration` which is `PGlobalUniqueDeclaration`)
    map.unique.values.flatMap { case (inScope, d) => {
      val canUnique = (d.isInstanceOf[PGlobalUniqueDeclaration] && !map.isGlobal) || (d.isInstanceOf[PMemberUniqueDeclaration] && !map.isMember)
      checkUnique(d, inScope && canUnique).map((d, _))
    }
    }.toSeq
  }

  def newRef(idnuse: PIdnUseName[_]) = {
    // assert(idnuse.decls.isEmpty, s"Encountered new `PIdnUseName` which wasn't new (${idnuse.name} at ${idnuse.pos._1}). This can happen when PAst nodes are not properly copied (e.g. with `deepCopyAll`) but instead alias.")
    decls.get(idnuse.name).toSeq.flatten.foreach(idnuse.newDecl)
    refs.getOrElseUpdate(idnuse.name, mutable.Buffer.empty) += idnuse
  }

  def clear() = {
    decls.clear()
    unique.clear()
    refs.clear()
  }

  def keys = decls.keys
}

/**
 * Resolves identifiers to their declaration. The important traits that relate to this are:
 * - `PDeclaration` marks a declaration of an identifier.
 * - `PIdnUseName` marks a use of an identifier (should be resolved).
 *
 * - `PScope` marks a scope.
 * - `PMember <: PScope` marks a member scope.
 * - `PLocalDeclaration`: a declaration that is visible within the containing scope.
 * - `PMemberDeclaration`: a declaration that is visible within the containing member.
 * - `PGlobalDeclaration`: a declaration that is visible within the program.
 *
 * - `PBackwardDeclaration`: a declaration that can be referenced before it is declared.
 * - `POverridesDeclaration`: a declaration that overrides any other previously seen declarations.
 *
 * - `PScopeUniqueDeclaration`: marks a declaration as unique within the scope.
 * - `PMemberUniqueDeclaration`: marks a declaration as unique within the member.
 * - `PGlobalUniqueDeclaration`: marks a declaration as unique within the program.
 *
 * - `PNameAnalyserOpaque` marks a scope as opaque (should not be traversed by the name analyser).
 */
case class NameAnalyser() {

  /** To record error messages */
  var messages: FastMessaging.Messages = Nil

  def success: Boolean = messages.isEmpty || messages.forall(m => !m.error)

  /** Resolves the global declaration to which the given identifier `name` refers.
   */
  def globalDefinitions(name: String): Seq[PDeclaration] = {
    globalDeclarationMap.decls.getOrElse(name, Nil).toSeq
  }

  def reset(): Unit = {
    globalDeclarationMap.clear()
    localDeclarationMaps.clear()
    namesInScope.clear()
  }

  private val globalDeclarationMap = DeclarationMap(isMember = false, isGlobal = true)

  /* [2014-11-13 Malte] Changed localDeclarationMaps to be a map from PScope.Id
   * instead of from PScope directly. This was necessary in order to support
   * changing PScopes during type-checking, e.g., when changing the type of a
   * variable bound by a let-expression. This change (potentially) affects the
   * hashcode of the let-expression (which is a PScope), which in turn affects
   * localDeclarationMaps because such that the value stored for scope cannot
   * be retrieved anymore.
   */
  private val localDeclarationMaps = mutable.HashMap[PScope.Id, DeclarationMap]()

  private val namesInScope = mutable.Set.empty[String]

  def check(g: PNode, target: Option[PNode], initialCurScope: PScope = null): Unit = {
    var curScope: PScope = initialCurScope

    def getMap(): DeclarationMap = Option(curScope).map(_.scopeId).map(localDeclarationMaps.get(_).get).getOrElse(globalDeclarationMap)

    val scopeStack = mutable.Stack[PScope]()
    var opaque = 0

    val nodeDownNameCollectorVisitor = new PartialFunction[PNode, Unit] {
      def apply(n: PNode) = {
        if (n == target.orNull)
          namesInScope ++= getMap().keys
        n match {
          // Opaque
          case _: PNameAnalyserOpaque =>
            opaque += 1
          case _ if opaque > 0 =>
          // Regular
          case d: PDeclaration =>
            // Add to declaration map
            val localDecls = getMap()
            localDecls.newDecl(d)
            val clashing = localDecls.checkUnique(d, true)
            if (clashing.isDefined)
              messages ++= FastMessaging.message(d.idndef, s"duplicate identifier `${d.idndef.name}` at ${d.idndef.pos._1} and at ${clashing.get.idndef.pos._1}")
          case i: PIdnUseName[_] if target.isEmpty =>
            getMap().newRef(i)
          case _ =>
        }

        n match {
          case _ if opaque > 0 =>
          case s: PScope =>
            localDeclarationMaps.put(s.scopeId, DeclarationMap(isMember = s.isInstanceOf[PMember]))
            scopeStack.push(curScope)
            curScope = s
          case _ =>
        }
      }

      def isDefinedAt(n: PNode) = {
        n match {
          case _: PDeclaration => true
          case _: PScope => true
          case _: PIdnUseName[_] => true
          case _: PNameAnalyserOpaque => true
          case _ => target.isDefined
        }
      }
    }

    val nodeUpNameCollectorVisitor = new PartialFunction[PNode, Unit] {
      def apply(n: PNode) = {
        n match {
          // Opaque
          case _: PNameAnalyserOpaque =>
            opaque -= 1
          case _ if opaque > 0 =>
          // Regular
          case _: PScope =>
            val popMap = localDeclarationMaps.get(curScope.scopeId).get
            val newScope = scopeStack.pop()
            curScope = newScope

            val clashing = getMap().merge(popMap)
            clashing.foreach { case (clashing, unique) =>
              messages ++= FastMessaging.message(clashing.idndef, s"duplicate identifier `${clashing.idndef.name}` at ${clashing.idndef.pos._1} and at ${unique.idndef.pos._1}")
            }
          case _ =>
        }
      }

      def isDefinedAt(n: PNode) = {
        n match {
          case _: PScope => true
          case _: PNameAnalyserOpaque => true
          case _ => false
        }
      }
    }

    // find all declarations
    g.visit(nodeDownNameCollectorVisitor, nodeUpNameCollectorVisitor)

    // If we started from some inner scope, walk all the way back out to the whole program
    // with a variation of nodeUpNameCollectorVisitor
    if (initialCurScope != null) {
      assert(initialCurScope == curScope)

      while (curScope != null) {
        val popMap = localDeclarationMaps.get(curScope.scopeId).get
        curScope.getAncestor[PScope] match {
          case Some(newScope) =>
            curScope = newScope
          case None =>
            curScope = null
        }
        getMap().merge(popMap)
      }
    }
  }

  def run(p: PProgram): Boolean = {
    check(p, None)
    success
  }

  def namesInScope(n: PNode, target: Option[PNode] = None): Set[String] = {
    check(n, target)
    (namesInScope ++ globalDeclarationMap.keys).toSet
  }
}
