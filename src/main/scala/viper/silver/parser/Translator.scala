// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import viper.silver.FastMessaging
import viper.silver.ast.utility._
import viper.silver.ast.{SourcePosition, _}
import viper.silver.plugin.standard.adt.{Adt, AdtType}

import scala.collection.mutable
import scala.language.implicitConversions

/**
 * Takes an abstract syntax tree after parsing is done and translates it into
 * a Viper abstract syntax tree.
 *
 * [2014-05-08 Malte] The current architecture of the resolver makes it hard
 * to detect all malformed ASTs. It is, for example, hard to detect that an
 * expression "f > 0", where f is an int-typed field, is malformed.
 * The translator can thus not assume that the input tree is completely
 * wellformed, and in cases where a malformed tree is detected, it does not
 * return a tree, but instead, records error messages using the
 * Messaging feature.
 */
case class Translator(program: PProgram) {

  case class MethodTemplate(generics: Seq[String], name: String, args: Seq[(String, Type)], ref: PMethod) {

  }

  case class DatatypeTemplate(generics: Seq[String], name: String, fields: Seq[(String, Type)]) {
    def getInstantiatedName(args: Seq[Type]): String = {
      val parameters = this.generics.map(g => TypeVar(g))
      val mapping = parameters.zip(args).toMap
      encodeTypeAsString(DatatypeType(this.name, mapping)(parameters))
    }
  }

  val datatypeTemplateInfos: scala.collection.mutable.Map[String, Seq[String]] = new mutable.HashMap[String, Seq[String]]()
  val datatypeTemplates: scala.collection.mutable.Map[String, DatatypeTemplate] = new mutable.HashMap[String, DatatypeTemplate]()
  val instantiatedDatatypes: scala.collection.mutable.Map[Type, Datatype] = new mutable.HashMap[Type, Datatype]()

  val methodTemplates: scala.collection.mutable.Map[String, MethodTemplate] = new mutable.HashMap[String, MethodTemplate]()
  val typeAnnotations: scala.collection.mutable.Map[String, (Seq[Type], Seq[Type])] = new mutable.HashMap[String, (Seq[Type], Seq[Type])]()
  val instantiatedMethods: scala.collection.mutable.Set[String] = new mutable.HashSet[String]()
  val coreMethods: scala.collection.mutable.Set[String] = new mutable.HashSet[String]()

  var translatedMethods: scala.collection.mutable.Map[String, Method] = new mutable.HashMap[String, Method]()
  var translatedDatatypes: scala.collection.mutable.Map[String, Datatype] = new mutable.HashMap[String, Datatype]()
  var translatedDomains: scala.collection.mutable.Map[String, Domain] = new mutable.HashMap[String, Domain]()

  // TODO CFG: ensure no generic predicates are folded/unfolded
  // TODO CFG: ensure generic predicate only have a single parameter

  def translate(tv: PTypeVarDecl): TypeVar = {
    TypeVar(tv.idndef.name)
  }

  def translate(pdfd: PDatatypeFieldDecl): DatatypeField = {
    val name = pdfd.idndef.name
    val typ = ttyp(pdfd.typ)
    DatatypeField(
      name, typ
    )()
  }

  def translate(pdatatype: PDatatype): Datatype = {
    val name = pdatatype.idndef.name
    val typeVars = pdatatype.typVars.map(d => d.inner.toSeq).getOrElse(Nil).map(v => translate(v))
    val fields = pdatatype.content.inner.flatMap(v => v.fields.toSeq).map(d => translate(d))

    Datatype(
      name,
      typeVars,
      fields,
    )()
  }

  def anding(es: Seq[Exp]): Exp = {
    es.reduceOption((a, b) => And(a, b)())
      .getOrElse(TrueLit()())
  }

  //  def generateRepresentation(datatype: Datatype): Predicate = {
  //    val fields = generateFields(datatype)
  //    val args = Seq(LocalVarDecl("this", Ref)())
  //    val thisVar = LocalVar("this", Ref)()
  //    datatype.content.map(f => {
  //      val args = Seq(FieldAccess(thisVar, fields.find(a => a.name.equals(f.name)).get))
  //      val predicateName = datatype.
  //      PredicateAccess(args, predicateName)()
  //    })
  //    val body = Some()
  //    Predicate(datatype.name, args, body)()
  //  }

  def encodeTypeListAsString(typ: Seq[Type]): String = {
    if (typ.isEmpty) ""
    else {
      val joined = typ.map(encodeTypeAsString)
        .reduceOption((a, b) => a + "$$$_" + b)
        .getOrElse("")
      s"${"$$_"}${joined}${"$$$$_"}"
    }
  }

  def getMethodTemplate(name: String): MethodTemplate = {
    if (!(methodTemplates.contains(name))) {
      throw new IllegalArgumentException(s"GETTING METHOD THAT IS UNKNOWN: ${name}")
    }
    methodTemplates(name)
  }

  def getDatatypeTemplate(name: String): DatatypeTemplate = {
    datatypeTemplates(name)
  }

  def isDatatype(typ: Type): Boolean = {
    typ match {
      case d: DatatypeType => true
      case _ => false
    }
  }

  def isDatatype(typ: PType): Boolean = {
    typ match {
      case d: PDomainType => {
        isDatatype(d.genericName)
      }
      case _ => false
    }
  }

  def isDatatype(name: String): Boolean = {
    datatypeTemplateInfos.contains(name)
  }

  def getDatatype(name: String): DatatypeTemplate = {
    datatypeTemplates(name)
  }

  def getDomain(name: String): Domain = {
    translatedDomains(name)
  }

  def encodeTypeAsString(typ: Type): String = {
    typ match {
      case inType: BuiltInType => inType match {
        case atomicType: AtomicType => atomicType match {
          case Int => "Int"
          case Bool => "Bool"
          case Perm => "Perm"
          case Ref => "Ref"
          case InternalType => "InternalType"
          case Wand => "Wand"
          case BackendType(viperName, _) => viperName
        }
        case collectionType: CollectionType => collectionType match {
          case SeqType(elementType) => s"Seq${encodeTypeListAsString(Seq(elementType))}"
          case SetType(elementType) => s"Set${encodeTypeListAsString(Seq(elementType))}"
          case MultisetType(elementType) => s"Multiset${encodeTypeListAsString(Seq(elementType))}"
        }
        case MapType(keyType, valueType) => s"Map${encodeTypeListAsString(Seq(keyType, valueType))}"
      }
      case extensionType: ExtensionType => ???
      case genericType: GenericType => genericType match {
        case DomainType(domainName, partialTypVarsMap) => s"${domainName}${encodeTypeListAsString(getDomain(domainName).typVars.map(v => partialTypVarsMap(v)))}"
        case DatatypeType(datatypeName, partialTypVarsMap) => {
          val args = getDatatype(datatypeName)
            .generics
            .map(g => TypeVar(g))
            .map(v => partialTypVarsMap(v))
          val generics = encodeTypeListAsString(args)
          s"${datatypeName}$generics"
        }
      }
      case TypeVar(name) => s"${"$$$$"}_${name}"
      case _ => ???
    }
  }

  //  def generateFields(datatype: Datatype): Seq[Field] = {
  //    datatype.content.map(f => Field(s"${DatatypeType(datatype)}${"$$$"}${f.name}"))
  //  }

  def getGenericParameterInfo(name: String): Seq[String] = {
    datatypeTemplateInfos(name)
  }

  def prepareDatatypeTemplates(dts: Seq[PDatatype]): Unit = {
    dts.foreach(d => {
      datatypeTemplateInfos.put(d.idndef.name, d.typVarsSeq.map(_.idndef.name))
    })

    println(s"preparing templates: ${dts}")
    dts.foreach(d => {
      println(s"preparing the datatype ${d.idndef.name}")
      val dt = DatatypeTemplate(
        d.typVarsSeq.map(_.idndef.name),
        d.idndef.name,
        d.containedFieldDecls.map(f => (f.idndef.name, ttyp(f.typ)))
      )
      datatypeTemplates.put(d.idndef.name, dt)
    })
  }

  def prepareMethodTemplates(mths: Seq[PMethod]): Unit = {
    mths.foreach(m => {
      val generics = m.typVars.map(_.inner.toSeq.map(a => a.idndef.name)).getOrElse(Nil)
      val name = m.idndef.name
      val args = m.args.inner.toSeq.map(a => (a.idndef.name, ttyp(a.typ)))
      val template = MethodTemplate(
        generics,
        name,
        args,
        m
      )
      coreMethods.add(m.idndef.name)
      methodTemplates.put(m.idndef.name, template)
    })
  }

  def translatePSeqn(seee: PSeqn): Seqn = {
    val pos = seee
    val (s, annotations) = extractAnnotationFromStmt(seee)
    val sourcePNodeInfo = SourcePNodeInfo(seee)
    val info = if (annotations.isEmpty) sourcePNodeInfo else ConsInfo(sourcePNodeInfo, AnnotationInfo(annotations))

    val seqn = seee.ss.inner.toSeq
    val plocals = seqn.collect {
      case l: PVars => Some(l)
      case _ => None
    }
    val locals = plocals.flatten.map {
      case p@PVars(_, vars, _) => {
        vars.toSeq.map(v => {
          val value = ttyp(v.typ) match {
            case _: DatatypeType => {
              Ref
            }
            case e => e
          }
          LocalVarDecl(v.idndef.name, value)(p, SourcePNodeInfo(v))
        })
      }
    }.flatten
    Seqn(seqn filterNot (_.isInstanceOf[PSkip]) map stmt, locals)(pos, info)
  }

  def translate: Option[Program] /*(Program, Seq[Messaging.Record])*/ = {
    // assert(TypeChecker.messagecount == 0, "Expected previous phases to succeed, but found error messages.") // AS: no longer sharing state with these phases

    val (pdomains, pfields, pfunctions, ppredicates, pmethods, pextensions, pdatatypes) =
      (program.domains, program.fields, program.functions, program.predicates, program.methods, program.extensions, program.datatypes)

    prepareDatatypeTemplates(pdatatypes)
    prepareMethodTemplates(pmethods)
    //    println("prepared templates")

    /* [2022-03-14 Alessandro] Domain signatures need no be translated first, since signatures of other declarations
      * like domain functions, and ordinary functions might depend on the domain signature. Especially this is the case
      * when signatures contain user-defined domain types. The same applies for extensions since they might introduce
      * new top-level declarations that behave similar as domains.
      */
    pdomains foreach translateMemberSignature
    pextensions foreach translateMemberSignature

    /* [2022-03-14 Alessandro] Following signatures can be translated independently of each other but must be translated
      * after signatures of domains and extensions because of the above mentioned reasons.
      */
    pdomains flatMap (_.funcs) foreach translateMemberSignature
    (pfields ++ pfunctions ++ ppredicates) foreach translateMemberSignature
    //    println("translated signatures")

    /* [2022-03-14 Alessandro] After the signatures are translated, the actual full translations can be done
      * independently of each other.
      */
    val extensions = pextensions map translate
    val domain = (pdomains map translate) ++ extensions filter (t => t.isInstanceOf[Domain])
    val fields = (pfields flatMap (_.fields.toSeq map translate)) ++ extensions filter (t => t.isInstanceOf[Field])
    val functions = (pfunctions map translate) ++ extensions filter (t => t.isInstanceOf[Function])
    val predicates = (ppredicates map translate) ++ extensions filter (t => t.isInstanceOf[Predicate])
    val datatypes = (pdatatypes map translate)

    //    println("translated everything except methods")

    val methods = (pmethods map translate) ++ extensions filter (t => t.isInstanceOf[Method])
    //    println("translated methods")
    //    val methods = (pmethods ++ extensions filter (t => t.isInstanceOf[Method])).filter(m => m.typVars.map(v => v.inner.toSeq.length).getOrElse(0) == 0) (pmethods map translate) ++ extensions filter (t => t.isInstanceOf[Method])
    //methods.head.asInstanceOf[Method].body.map(b => b.)

    // start tracing the methods from ones with no generic parameters

    val filteredFields: Seq[Field] = members.values
      .filter(_.isInstanceOf[Field])
      .map(_.asInstanceOf[Field])
      .toSeq

    val filteredPredicates: Seq[Predicate] = members.values
      .filter(_.isInstanceOf[Predicate])
      .map(_.asInstanceOf[Predicate])
      .toSeq

    val filteredMethods: Seq[Method] = members.values
      .filter(_.isInstanceOf[Method])
      .map(_.asInstanceOf[Method])
      .toSeq


    val finalProgram = ImpureAssumeRewriter.rewriteAssumes(Program(domain.asInstanceOf[Seq[Domain]], filteredFields,
      functions.asInstanceOf[Seq[Function]], filteredPredicates, filteredMethods,
      (extensions filter (t => t.isInstanceOf[ExtensionMember])).asInstanceOf[Seq[ExtensionMember]],
      InferInfo(typeAnnotations.toMap))(program))

    //    println("METHODS:")
    //    filteredMethods.foreach(m => println(m.name, m.pres))


    finalProgram.deepCollect {
      case fp: ForPerm => Consistency.checkForPermArguments(fp, finalProgram)
      case trig: Trigger => Consistency.checkTriggers(trig, finalProgram)
    }

    //    println("FIELDS:")
    //    filteredFields.foreach(println)

    println(s"C MESSAGES: ${Consistency.messages}")

    if (Consistency.messages.isEmpty) Some(finalProgram) // all error messages generated during translation should be Consistency messages
    else None
  }

  private def translate(t: PExtender): Member = {
    t.translateMember(this)
  }

  private def translate(m: PMethod): Method = m match {
    case PMethod(_, _, idndef, gens, args, _, pres, posts, body) =>
      instantiateMethodTemplate(idndef.name, args.inner.toSeq.map(_.typ))

      //      val m = findMethod(idndef)
      //      val genericParameters = gens.map(v => v.inner.toSeq).getOrElse(Nil).map(a => a.idndef.name)
      //        .foldRight("")((a, b) => a + "$" + b)
      //
      //      val newBody = body.map(actualBody => stmt(actualBody).asInstanceOf[Seqn])
      //
      //      println(s"PRES BEFORE: ${pres}")
      //      println(s"PROCESSED PRES: ${pres.toSeq map (p => exp(p.e))}")
      //
      //      val finalMethod = m.copy(
      //        name = m.name + genericParameters,
      //        formalArgs = m.formalArgs.map(l => l.copy(typ = convertToViperType(l.typ))(l.pos, l.info, l.errT)),
      //        pres = pres.toSeq map (p => exp(p.e)),
      //        posts = posts.toSeq map (p => exp(p.e)),
      //        body = newBody)(m.pos, m.info, m.errT)
      //
      //      println(s"FINAL METHOD: ${finalMethod.pres}")
      //      println(s"FINAL METHOD: ${finalMethod}")
      //
      //      members(finalMethod.name) = finalMethod
      //      finalMethod

      null
  }

  private def translate(d: PDomain): Domain = d match {
    case pd@PDomain(_, _, name, _, interpretation, _) =>
      val d = findDomain(name)
      val dd = d.copy(functions = pd.funcs map (f => findDomainFunction(f.idndef)),
        axioms = pd.axioms map translate, interpretations = interpretation.map(_.interps))(d.pos, d.info, d.errT)
      members(d.name) = dd
      translatedDomains(dd.name) = dd
      dd
  }

  private def translate(a: PAxiom): DomainAxiom = a match {
    case pa@PAxiom(anns, _, Some(name), e) =>
      NamedDomainAxiom(name.name, exp(e.e.inner))(a, Translator.toInfo(anns, pa), domainName = pa.domain.idndef.name)
    case pa@PAxiom(anns, _, None, e) =>
      AnonymousDomainAxiom(exp(e.e.inner))(a, Translator.toInfo(anns, pa), domainName = pa.domain.idndef.name)
  }

  private def translate(f: PFunction): Function = f match {
    case PFunction(_, _, idndef, _, _, _, pres, posts, body) =>
      val f = findFunction(idndef)
      val ff = f.copy(pres = pres.toSeq map (p => exp(p.e)), posts = posts.toSeq map (p => exp(p.e)), body = body map (_.e.inner) map exp)(f.pos, f.info, f.errT)
      members(f.name) = ff
      ff
  }

  private def translate(p: PPredicate): Predicate = p match {
    case PPredicate(_, _, idndef, _, _, body) =>
      val p = findPredicate(idndef)
      val pp = p.copy(body = body map (_.e.inner) map exp)(p.pos, p.info, p.errT)
      members(p.name) = pp
      pp
  }

  private def translate(f: PFieldDecl) = findField(f.idndef)

  protected val members: mutable.Map[String, Node] = collection.mutable.HashMap[String, Node]()

  def getMembers() = members

  /**
   * Translate the signature of a member, so that it can be looked up later.
   *
   * TODO: Get rid of this method!
   *         - Passing lots of null references is just asking for trouble
   *         - It should no longer be necessary to have this lookup table because, e.g. a
   *           method call no longer needs the method node, the method name (as a string)
   *           suffices
   */
  private def translateMemberSignature(p: PMember): Unit = p.declares foreach { decl =>
    val pos = decl
    val name = decl.idndef.name
    val t = decl match {
      case pf@PFieldDecl(_, _, typ) =>
        Field(name, ttyp(typ))(pos, Translator.toInfo(p.annotations, pf))
      case pf@PFunction(_, _, _, _, _, typ, _, _, _) =>
        Function(name, pf.formalArgs map liftArgDecl, ttyp(typ), null, null, null)(pos, Translator.toInfo(p.annotations, pf))
      case pdf@PDomainFunction(_, unique, _, _, _, _, typ, interp) =>
        DomainFunc(name, pdf.formalArgs map liftAnyArgDecl, ttyp(typ), unique.isDefined, interp.map(_.i.str))(pos, Translator.toInfo(p.annotations, pdf), pdf.domain.idndef.name)
      case pd@PDomain(_, _, _, typVars, interp, _) =>
        Domain(name, null, null, typVars map (_.inner.toSeq map (t => TypeVar(t.idndef.name))) getOrElse Nil, interp.map(_.interps))(pos, Translator.toInfo(p.annotations, pd))
      case pp: PPredicate =>
        Predicate(name, pp.formalArgs map liftArgDecl, null)(pos, Translator.toInfo(p.annotations, pp))
      case pm: PMethod =>
        pm.args.inner.toSeq.map(d => d.typ)
          .map(a => ttyp(a))
          .foreach(t => instantiateDatatypeTemplate(t))
        Method(name, pm.formalArgs map liftArgDecl, pm.formalReturns map liftReturnDecl, null, null, null)(pos, Translator.toInfo(p.annotations, pm))
    }
    members.put(decl.idndef.name, t)
  }

  private def translateMemberSignature(p: PExtender): Unit = {
    p match {
      case _: PMember =>
        val l = p.translateMemberSignature(this)
        members.put(l.name, l)
    }
  }

  // helper methods that can be called if one knows what 'id' refers to
  private def findDomain(id: PIdentifier) = members(id.name).asInstanceOf[Domain]

  private def findField(id: PIdentifier) = members(id.name).asInstanceOf[Field]

  private def findDatatypeField(typ: Type, id: PIdentifier) = {
    members(encodeTypeAsString(typ) + "$$$" + id.name).asInstanceOf[Field]
  }

  private def findFunction(id: PIdentifier) = members(id.name).asInstanceOf[Function]

  private def findDomainFunction(id: PIdentifier) = members(id.name).asInstanceOf[DomainFunc]

  private def findPredicate(id: PIdentifier) = members(id.name).asInstanceOf[Predicate]

  private def findMethod(id: PIdentifier) = members(id.name).asInstanceOf[Method]

  def generatePredicateOfType(dtPrefix: String, fieldName: String, typ: Type): Option[Exp] = {
    val encodedSignature = encodeTypeAsString(typ)
    typ match {
      case dt: DatatypeType => {
        val onePerm = FractionalPerm(IntLit(1)(), IntLit(1)())()
        val zeroPerm = FractionalPerm(IntLit(0)(), IntLit(1)())()

        val valFieldAccess = FieldAccess(LocalVar("this", Ref)(), Field(fieldName, Ref)())()
        val permissionFieldAccess = FieldAccess(LocalVar("this", Ref)(), Field(s"${fieldName}${"$"}P", Perm)())()

        val predAccess = PredicateAccess(Seq(valFieldAccess), encodedSignature)()
        val predAccPred = PredicateAccessPredicate(predAccess, Some(permissionFieldAccess))()
        val guarded = Implies(NeCmp(valFieldAccess, NullLit()())(), predAccPred)()

        val permFieldPredAccess = FieldAccessPredicate(permissionFieldAccess, Some(onePerm))()

        val permissionRange = And(LeCmp(zeroPerm, permissionFieldAccess)(), LeCmp(permissionFieldAccess, onePerm)())()


        Some(And(And(permFieldPredAccess, permissionRange)(), guarded)())
      }
      case _ => None
    }
  }

  def generatePredicateContent(typ: Type, dtPrefix: String, dt: Datatype): Exp = {
    val predicateAccesses = anding(dt.content.flatMap(f => {
      val fieldName = dtPrefix + "$$$" + f.name.replaceFirst(".*\\$", "")
      generatePredicateOfType(dtPrefix, fieldName, f.typ)
    }))
    // TODO CFG: add recursive permission equalities
    val fieldAccesses = anding(dt.content.map(f => {
      val fieldName = dtPrefix + "$$$" + f.name.replaceFirst(".*\\$", "")
      val predAccess = FieldAccess(LocalVar("this", Ref)(), Field(fieldName, convertToViperType(f.typ))())()
      val permExp = Some(FractionalPerm(IntLit(1)(), IntLit(1)())())
      FieldAccessPredicate(predAccess, permExp)()
    }))
    And(fieldAccesses, predicateAccesses)()
  }

  def substituteTypeParameters(d: DatatypeType): Datatype = {
    val temp = getDatatypeTemplate(d.genericName)
    val replacement = temp.generics.map(g => TypeVar(g)).zip(d.typeArguments).toMap
    val fields = temp.fields.map(f => DatatypeField(f._1, f._2.substitute(replacement))())
    Datatype(
      temp.name,
      Seq(),
      fields
    )()
  }

  def convertToViperType(typ: Type): Type = {
    typ match {
      case _: DatatypeType => Ref
      case _: TypeVar => Ref
      case e => e
    }
  }

  def generateFields(typ: Type, instantiated: Datatype): Seq[Field] = {
    val encodedSignature = encodeTypeAsString(typ)
    instantiated.content.map(f => {
      val fieldName = encodedSignature + "$$$" + f.name.replaceFirst(".*\\$", "")
      val afterConversion = convertToViperType(f.typ)
      Field(fieldName, afterConversion)()
    })
  }

  def generatePermissionFields(typ: Type, instantiated: Datatype): Seq[Field] = {
    val encodedSignature = encodeTypeAsString(typ)
    instantiated.content.flatMap(f => {
      f.typ match {
        case d: DatatypeType => {
          val fieldName = encodedSignature + "$$$" + f.name.replaceFirst(".*\\$", "") + "$P"
          Seq(Field(fieldName, Perm)())
        }
        case e => Seq()
      }
    })
  }

  def generateDatatypePredicate(typ: Type, instantiated: Datatype): Predicate = {
    val encodedSignature = encodeTypeAsString(typ)
    val body = generatePredicateContent(typ, encodedSignature, instantiated)
    Predicate(
      encodedSignature,
      Seq(LocalVarDecl("this", Ref)()),
      Some(body)
    )()
  }

  def generateDatatypeMakeMethod(typ: Type, instantiated: Datatype): Method = {
    val encodedSignature = encodeTypeAsString(typ)
    val makeName = s"make${"$"}${encodedSignature}"

    val valArgs = instantiated.content.map(v => LocalVarDecl(v.name, convertToViperType(v.typ))())
    val permArgs = instantiated.content.flatMap(v => if (isDatatype(v.typ)) Some(v.name + "$P") else None)
      .map(f => LocalVarDecl(f, Perm)())
    val args = valArgs ++ permArgs

    val returns = Seq(LocalVarDecl("this", Ref)())

    typeAnnotations.put(makeName, (instantiated.content.map(v => v.typ) ++ permArgs.map(a => a.typ), Seq(typ)))

    // TODO: add permissions to all the transitive predicates as preconditions
    // TODO: REACTIVATE WHEN REQUIRES ARE NOT INTRODUCED BLINDLY
    val transPredAccess = Seq()
//    instantiated.content
//      .filter(v => isDatatype(v.typ))
//      .map(v => {
//        val valParam = LocalVar(v.name, Ref)()
//        val permParam = LocalVar(v.name + "$P", Perm)()
//        val predSignature = encodeTypeAsString(v.typ)
//        val predAccess = PredicateAccess(Seq(valParam), predSignature)()
//        val predAccPred = PredicateAccessPredicate(predAccess, Some(permParam))()
//        Implies(NeCmp(valParam, NullLit()())(), predAccPred)()
//      })

    val permRangeGuard = instantiated.content
      .filter(v => isDatatype(v.typ))
      .map(v => {
        val onePerm = FractionalPerm(IntLit(1)(), IntLit(1)())()
        val zeroPerm = FractionalPerm(IntLit(0)(), IntLit(1)())()
        val varAccess = LocalVar(v.name + "$P", Perm)()
        And(LeCmp(zeroPerm, varAccess)(), LeCmp(varAccess, onePerm)())()
      })

    // TODO: add permission equality to the recursive datatype predicates

    // MAKE STATEMENTS NEED TO INCORPORATE
    val preconditions = permRangeGuard ++ transPredAccess

    val finalPredAccess = PredicateAccessPredicate(
      PredicateAccess(Seq(LocalVar("this", Ref)()), encodedSignature)(),
      None
    )()

    val valParamEqValInObj = instantiated.content
      .map(v => {
        val fieldName = encodedSignature + "$$$" + v.name.replaceFirst(".*\\$", "")
        val fieldTyp = convertToViperType(v.typ)
        val field = Field(fieldName, fieldTyp)()
        val paramVar = LocalVar(v.name, fieldTyp)()
        val thisVar = LocalVar("this", Ref)()
        val fieldAccess = FieldAccess(thisVar, field)()
        Unfolding(finalPredAccess, EqCmp(fieldAccess, paramVar)())()
      })

    val permParamEqValInObj = instantiated.content
      .filter(v => isDatatype(v.typ))
      .map(v => {
        val fieldName = encodedSignature + "$$$" + v.name.replaceFirst(".*\\$", "") + "$P"
        val field = Field(fieldName, Perm)()
        val paramVar = LocalVar(v.name + "$P", Perm)()
        val thisVar = LocalVar("this", Ref)()
        val fieldAccess = FieldAccess(thisVar, field)()
        Unfolding(finalPredAccess, EqCmp(fieldAccess, paramVar)())()
      })

    /* TODO: REINTRODUCE WHEN NOT INSERTED BLINDLY: Seq(finalPredAccess) */
    val postconditions = Seq()  ++ valParamEqValInObj ++ permParamEqValInObj

    val objValFields = instantiated.content
      .map(v => {
        val fieldName = encodedSignature + "$$$" + v.name.replaceFirst(".*\\$", "")
        val fieldTyp = convertToViperType(v.typ)
        Field(fieldName, fieldTyp)()
      })

    val objPermFields = instantiated.content
      .filter(v => isDatatype(v.typ))
      .map(v => {
        val fieldName = encodedSignature + "$$$" + v.name.replaceFirst(".*\\$", "") + "$P"
        Field(fieldName, Perm)()
      })


    val objCreation = NewStmt(LocalVar("this", Ref)(), objValFields ++ objPermFields)()

    val valSetting = instantiated.content
      .map(v => {
        val fieldName = encodedSignature + "$$$" + v.name.replaceFirst(".*\\$", "")
        val fieldTyp = convertToViperType(v.typ)
        val accessedField = Field(fieldName, fieldTyp)()
        val fieldAccess = FieldAccess(LocalVar("this", Ref)(), accessedField)()
        val value = LocalVar(v.name, fieldTyp)()
        FieldAssign(fieldAccess, value)()
      })

    val permSetting = instantiated.content
      .filter(v => isDatatype(v.typ))
      .map(v => {
        val fieldName = encodedSignature + "$$$" + v.name.replaceFirst(".*\\$", "") + "$P"
        val accessedField = Field(fieldName, Perm)()
        val fieldAccess = FieldAccess(LocalVar("this", Ref)(), accessedField)()
        val value = LocalVar(v.name + "$P", Perm)()
        FieldAssign(fieldAccess, value)()
      })

    val body = Seqn(Seq(objCreation) ++ valSetting ++ permSetting, Seq())()

    Method(
      makeName,
      args,
      returns,
      preconditions,
      postconditions,
      Some(body)
    )()
  }

  def addMember(m: Member): Unit = {
    members.put(m.name, m)
  }

  def addAllMembers[T <: Member](mems: Seq[T]): Unit = {
    mems.foreach(m => {
      addMember(m)
    })
  }

  def instantiateDatatypeTemplate(typ: Type) = {
    // TODO CFG: ADD METHOD TO MAKE AN INSTANCE WHICH IS A STUB WITH NO BODY
    typ match {
      case d: DatatypeType => {
        if (!(instantiatedDatatypes.contains(typ))) {
          val instantiated = substituteTypeParameters(d)
          instantiatedDatatypes.put(typ, instantiated)
          val fields = generateFields(typ, instantiated)
          addAllMembers(fields)
          val permFields = generatePermissionFields(typ, instantiated)
          addAllMembers(permFields)


          // adding field members with the encoded name for the instantiated parameters


          val predicate = generateDatatypePredicate(typ, instantiated)
          val method = generateDatatypeMakeMethod(typ, instantiated)

          addMember(method)
          addMember(predicate)

          //          println("PREDICATE:")
          //          println(predicate.toString())
          //
          //          println("METHOD:")
          //          println(method.toString())
        }
      }
      case _ =>
    }
  }

  def instantiateMethodTemplate(methodName: String, args: Seq[PType]): Unit = {
    //    println(s"instantiating method ${methodName} with ${args}")
    val temp = getMethodTemplate(methodName)
    val error = (node: PNode) => (msg: String) => {
      println(s"instantiation error: ${msg}")
    }
    val result = Unification.findUnificationForArgs(error, temp.ref, temp.ref.args.inner.toSeq.map(a => a.typ).zip(args))
    //    println(s"UNIFICATION RESULT: ${result}")
    // instantiating the datatype instances of the arguments
    args.foreach(a => {
      instantiateDatatypeTemplate(ttyp(a))
    })

    val mapping: mutable.HashMap[String, PType] = mutable.HashMap.from(result.get)
    temp.generics.filter(g => !(result.get.contains(g)))
      .map(g => (g, PPrimitiv(PReserved(PKw.Ref)(temp.ref.pos))()))
      .foreach(kv => {
        mapping.put(kv._1, kv._2)
      })

    val map: Map[String, PType] = mapping.toMap

    val substitution = PTypeSubstitution(map)

    //    println(")))))))))))))))))))))))))))")
    //    println(s"SUB: ${substitution}")
    //    println(")))))))))))))))))))))))))))")

    // usually use a deep copy
    val adjustedBody = temp.ref.body.map(b => ParameterSubstitutor.processParametersSeqn(b, substitution))

    val presConverted = ParameterSubstitutor.processInvsSpecs(temp.ref.pres, substitution)
      .specs
      .toSeq
      .map(v => v.e)
      .map(exp)

    val postsConverted = ParameterSubstitutor.processInvsSpecs(temp.ref.posts, substitution)
      .specs
      .toSeq
      .map(v => v.e)
      .map(exp)

    val returningMapped = temp.ref.returns.map(m => m.formalReturns.inner
        .toSeq
        .map(r => (r.idndef.name, ttyp(r.typ))))
      .getOrElse(Nil)

    val returning = returningMapped
      .map(r => LocalVarDecl(
        r._1,
        convertToViperType(r._2))())

    val adjustedName = temp.ref.idndef.name + "$" + encodeTypeListAsString(args.map(ttyp))
    val argsMapped = temp.ref.formalArgs
      .map(a => (a.idndef.name, ttyp(a.typ.substitute(substitution))))
    println(s"${adjustedName} => ${argsMapped} ${substitution}")
    val replacedArgs = argsMapped
      .map(a => LocalVarDecl(a._1, convertToViperType(a._2))())

    if (!instantiatedMethods.contains(adjustedName)) {

      typeAnnotations.put(adjustedName, (argsMapped.map(_._2), returningMapped.map(_._2)))
      instantiatedMethods.add(adjustedName)

      // add the method without body to prevent infinite cycles
      addMember(Method(
        adjustedName,
        replacedArgs,
        returning,
        presConverted,
        postsConverted,
        None
      )(temp.ref, NoInfo))



      val translatedBody = adjustedBody.map(b => translatePSeqn(b))
      addMember(Method(
        adjustedName,
        replacedArgs,
        returning,
        presConverted,
        postsConverted,
        translatedBody
      )(temp.ref, NoInfo))
    }
  }

  /** Takes a `PStmt` and turns it into a `Stmt`. */
  def stmt(pStmt: PStmt): Stmt = {
    val pos = pStmt
    val (s, annotations) = extractAnnotationFromStmt(pStmt)
    val sourcePNodeInfo = SourcePNodeInfo(pStmt)
    val info = if (annotations.isEmpty) sourcePNodeInfo else ConsInfo(sourcePNodeInfo, AnnotationInfo(annotations))
    s match {
      case PAssign(targets, _, PCall(method, args, _)) if coreMethods.contains(method.name) => {
        instantiateMethodTemplate(method.name, args.inner.toSeq.map(e => e.typ))
        val methodName = method.name + "$" + encodeTypeListAsString(args.inner.toSeq.map(e => e.typ).map(ttyp))
        val foundMethod = members(methodName).asInstanceOf[Method]
        //        println(s"calling method: ${methodName}")
        methodCallAssign(s, targets.toSeq, ts => MethodCall(foundMethod, args.inner.toSeq map exp, ts)(pos, info))
      }
      case PAssign(targets, _, PMakeExp(_, typ, args)) => {
        // instantiate datatype template
        val translatedType = ttyp(typ)
        instantiateDatatypeTemplate(translatedType)
        /*
        Encode the make as a method call:

        make List[Int](123, null)

        make$List$Int$(123, null, 1/1)

        the 1/1 is the permission for the transitive predicate access right (access to the predicate in next)

        TODO: remove the makestmt

        */
        //methodCallAssign(s, Seq(targets.head), ts => MakeStmt(ts.head, ttyp(typ), args.inner.toSeq map exp)(pos, info))
        //        println("targets:")
        //        targets.toSeq.foreach(t => {
        //          println(t, t.typ)
        // TODO: figure out how to adjust the types of the targets to match the viper encoding types
        //t.typ = convertToViperType(ttyp(t.typ))
        //        })

        methodCallAssign(s, targets.toSeq, ts => {
          val instantiated = instantiatedDatatypes(translatedType)
          val makeMethod = members("make$" + encodeTypeAsString(translatedType)).asInstanceOf[Method]
          val valExp = args.inner.toSeq map exp
          val permExp = instantiated.content.filter(v => isDatatype(v.typ))
            .map(_ => FractionalPerm(IntLit(1)(), IntLit(1)())())

          MethodCall(makeMethod, valExp ++ permExp, ts)(pos, info)
        })
      }
      case PAssign(targets, _, _) if targets.length != 1 =>
        sys.error(s"Found non-unary target of assignment")
      case PAssign(targets, _, PNewExp(_, fieldsOpt)) =>
        val fields = fieldsOpt.inner match {
          // Note that this will not use any fields that extensions declare
          case Left(_) => program.fields flatMap (_.fields.toSeq map translate)
          case Right(pfields) => pfields.toSeq map findField
        }
        methodCallAssign(s, Seq(targets.head), lv => NewStmt(lv.head, fields)(pos, info))
      case PAssign(PDelimited(idnuse: PIdnUseExp), _, rhs) =>
        LocalVarAssign(LocalVar(idnuse.name, ttyp(idnuse.decl.get.asInstanceOf[PAssignableVarDecl].typ))(pos, SourcePNodeInfo(idnuse)), exp(rhs))(pos, info)
      case a@PAssign(PDelimited(field: PFieldAccess), _, rhs) => {
        if (isDatatype(field.rcv.typ)) {
          //          println(s"FINDING DATATYPE FIELD: ${field.rcv.typ} -> ${field.idnref.name}")
          val resultingField = findDatatypeField(ttyp(field.rcv.typ), field.idnref)
          println(resultingField)
          val transformedRHS = exp(rhs)
          //          println(s"TRANS RHS: ${transformedRHS}     ${transformedRHS.typ}")
          FieldAssign(FieldAccess(exp(field.rcv), resultingField)(field, SourcePNodeInfo(field)), transformedRHS)(pos, info)
        }
        else {
          // TODO CFG: select the field with the given type associated :)
          //          println(s"FINDING FIELD: ${field.rcv.typ} -> ${field.idnref.name} ${a.pretty}")
          FieldAssign(FieldAccess(exp(field.rcv), findField(field.idnref))(field, SourcePNodeInfo(field)), exp(rhs))(pos, info)
        }
      }
      case lv: PVars =>
        // there are no declarations in the Viper AST; rather they are part of the scope signature
        lv.assign map stmt getOrElse Statements.EmptyStmt
      case p@PSeqn(ss) => translatePSeqn(p)

      case PFold(_, e) =>
        Fold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos, info)
      case PUnfold(_, e) =>
        Unfold(exp(e).asInstanceOf[PredicateAccessPredicate])(pos, info)
      case PPackageWand(_, e, proofScript) =>
        val wand = exp(e).asInstanceOf[MagicWand]
        Package(wand, proofScript map (stmt(_).asInstanceOf[Seqn]) getOrElse Statements.EmptyStmt)(pos, info)
      case PApplyWand(_, e) =>
        Apply(exp(e).asInstanceOf[MagicWand])(pos, info)
      case PInhale(_, e) =>
        Inhale(exp(e))(pos, info)
      case PAssume(_, e) =>
        Assume(exp(e))(pos, info)
      case PExhale(_, e) =>
        Exhale(exp(e))(pos, info)
      case PAssert(_, e) =>
        Assert(exp(e))(pos, info)
      case PLabel(_, name, invs) =>
        Label(name.name, invs.toSeq map (_.e) map exp)(pos, info)
      case PGoto(_, label) =>
        Goto(label.name)(pos, info)
      case PIf(_, cond, thn, els) =>
        If(exp(cond.inner), stmt(thn).asInstanceOf[Seqn], els map (stmt(_) match {
          case s: Seqn => s
          case s => Seqn(Seq(s), Nil)(s.pos, s.info)
        }) getOrElse Statements.EmptyStmt)(pos, info)
      case PElse(_, els) => stmt(els)
      case PWhile(_, cond, invs, body) =>
        While(exp(cond.inner), invs.toSeq map (inv => exp(inv.e)), stmt(body).asInstanceOf[Seqn])(pos, info)
      case PQuasihavoc(_, lhs, e) =>
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        Quasihavoc(newLhs, newE)(pos, info)
      case PQuasihavocall(_, vars, _, lhs, e) =>
        val newVars = vars.toSeq map liftLogicalDecl
        val (newLhs, newE) = havocStmtHelper(lhs, e)
        Quasihavocall(newVars, newLhs, newE)(pos, info)
      case t: PExtender => t.translateStmt(this)
      case _: PDefine | _: PSkip =>
        sys.error(s"Found unexpected intermediate statement $s (${s.getClass.getName}})")
    }
  }

  /**
   * Translates a simple PAst `a, b, c := methodCall(...)` to an Ast `a, b, c := methodCall(...)`. But if any
   * targets are field accesses, then the translation is from `(exprA).f, b, (exprC).g := methodCall(...)` to
   * ```
   * {(scopedDecls: _receiver0, _target0, _receiver2, _target2)
   * _receiver0 := exprA
   * _receiver2 := exprC
   * _target0, b, _target2 := methodCall(...)
   * _receiver0.f := _target0
   * _receiver2.g := _target2
   * }
   * ```
   */
  def methodCallAssign(errorNode: PNode, targets: Seq[PExp with PAssignTarget], assign: Seq[LocalVar] => Stmt): Stmt = {
    println("assign targets: ")
    val tTargets = targets map exp
    tTargets.foreach(e => println(e, e.typ))
    val ts = tTargets.zipWithIndex.map {
      case (lv: LocalVar, _) => (None, lv)
      case (fa: FieldAccess, i) => {
        // --- Before the call ---
        val rcvDecl = LocalVarDecl(s"_receiver$i", fa.rcv.typ)()
        val tgtDecl = LocalVarDecl(s"_target$i", fa.typ)()
        // From the example translation above for the first target the values are:
        // rcvUse: `_receiver0`
        val rcvUse = LocalVar(rcvDecl.name, rcvDecl.typ)(fa.rcv.pos)
        // rcvInit: `_receiver0 := exprA`
        val rcvInit = LocalVarAssign(rcvUse, fa.rcv)(fa.rcv.pos)
        // --- After the call ---
        // tgtUse: `_target0`
        val tgtUse = LocalVar(tgtDecl.name, tgtDecl.typ)(fa.pos)
        // rcvFa: `_receiver0.f`
        val rcvFa = FieldAccess(rcvUse, fa.field)(fa.pos, fa.info, NodeTrafo(fa) + fa.errT)
        // faAssign: `_receiver0.f := _target0`
        val faAssign = FieldAssign(rcvFa, tgtUse)(rcvFa.pos)
        (Some((rcvDecl, tgtDecl, rcvInit, faAssign)), tgtUse)
      }
      case _ => sys.error(s"Found invalid target of assignment")
    }

    //    println(s"TS: ${ts}")
    //    println(s"ASSIGN: ${assign}")
    val assn = assign(ts.map(_._2))
    val tmps = ts.flatMap(_._1)
    if (tmps.isEmpty)
      return assn
    if (!Consistency.noDuplicates(tmps.map(_._4.lhs.field)))
      Consistency.messages ++= FastMessaging.message(errorNode, s"multiple targets which access the same field are not allowed")
    Seqn(
      tmps.map(_._3) ++
        Seq(assn) ++
        tmps.map(_._4),
      tmps.flatMap(t => Seq(t._1, t._2))
    )(assn.pos, assn.info)
  }

  /** Helper function that translates subexpressions common to a Havoc or Havocall statement */
  def havocStmtHelper(lhs: Option[(PExp, _)], e: PExp): (Option[Exp], ResourceAccess) = {
    val newLhs = lhs.map(lhs => exp(lhs._1))
    exp(e) match {
      case exp: FieldAccess => (newLhs, exp)
      case PredicateAccessPredicate(predAccess, perm) =>
        // A PrediateAccessPredicate is a PredicateResourceAccess combined with
        // a Permission. Havoc expects a ResourceAccess. To make types match,
        // we must extract the PredicateResourceAccess.
        assert(perm.isEmpty || perm.get.isInstanceOf[FullPerm])
        (newLhs, predAccess)
      case exp: MagicWand => (newLhs, exp)
      case _ => sys.error("Can't havoc this kind of expression")
    }
  }

  def extractAnnotation(pexp: PExp): (PExp, Map[String, Seq[String]]) = {
    pexp match {
      case PAnnotatedExp(ann, e) =>
        val (resPexp, innerMap) = extractAnnotation(e)
        val combinedValue = if (innerMap.contains(ann.key.str)) {
          ann.values.inner.toSeq.map(_.str) ++ innerMap(ann.key.str)
        } else {
          ann.values.inner.toSeq.map(_.str)
        }
        (resPexp, innerMap.updated(ann.key.str, combinedValue))
      case _ => (pexp, Map())
    }
  }

  def extractAnnotationFromStmt(pStmt: PStmt): (PStmt, Map[String, Seq[String]]) = {
    pStmt match {
      case PAnnotatedStmt(ann, s) =>
        val (resPStmt, innerMap) = extractAnnotationFromStmt(s)
        val combinedValue = if (innerMap.contains(ann.key.str)) {
          ann.values.inner.toSeq.map(_.str) ++ innerMap(ann.key.str)
        } else {
          ann.values.inner.toSeq.map(_.str)
        }
        (resPStmt, innerMap.updated(ann.key.str, combinedValue))
      case _ => (pStmt, Map())
    }
  }

  /** Takes a `PExp` and turns it into an `Exp`. */
  def exp(parseExp: PExp): Exp = {
    val pos = parseExp
    val (pexp, annotationMap) = extractAnnotation(parseExp)
    val sourcePNodeInfo = SourcePNodeInfo(parseExp)
    val info = if (annotationMap.isEmpty) sourcePNodeInfo else ConsInfo(sourcePNodeInfo, AnnotationInfo(annotationMap))
    expInternal(pexp, pos, info)
  }

  // TODO: the encoded signature of the datatype is the default one without replacement -> failed type matching

  protected def expInternal(pexp: PExp, pos: PExp, info: Info): Exp = {
    pexp match {
      case PIdnUseExp(piu) =>
        piu.decl match {
          case Some(_: PTypedVarDecl) => {
            val value = ttyp(pexp.typ) match {
              case _: DatatypeType => Ref
              case _: TypeVar => Ref
              case e => e
            }
            LocalVar(piu.name, value)(pos, info)
          }
            // A malformed AST where a field, function or other declaration is used as a variable.
            // Should have been caught by the type checker.
          case _ => sys.error("should not occur in type-checked program")
        }
      case pbe@PBinExp(left, op, right) =>
        val (l, r) = (exp(left), exp(right))
        op.rs match {
          case PSymOp.Plus =>
            r.typ match {
              case Int => Add(l, r)(pos, info)
              case Perm => PermAdd(l, r)(pos, info)
              case _ => sys.error("should not occur in type-checked program")
            }
          case PSymOp.Minus =>
            r.typ match {
              case Int => Sub(l, r)(pos, info)
              case Perm => PermSub(l, r)(pos, info)
              case _ => sys.error("should not occur in type-checked program")
            }
          case PSymOp.Mul =>
            r.typ match {
              case Int =>
                l.typ match {
                  case Int => Mul(l, r)(pos, info)
                  case Perm => IntPermMul(r, l)(pos, info)
                  case _ => sys.error("should not occur in type-checked program")
                }
              case Perm =>
                l.typ match {
                  case Int => IntPermMul(l, r)(pos, info)
                  case Perm => PermMul(l, r)(pos, info)
                  case _ => sys.error("should not occur in type-checked program")
                }
              case _ => sys.error("should not occur in type-checked program")
            }
          case PSymOp.Div =>
            l.typ match {
              case Perm => r.typ match {
                case Int => PermDiv(l, r)(pos, info)
                case Perm => PermPermDiv(l, r)(pos, info)
              }
              case Int =>
                assert(r.typ == Int)
                if (ttyp(pbe.typ) == Int)
                  Div(l, r)(pos, info)
                else
                  FractionalPerm(l, r)(pos, info)
              case _ => sys.error("should not occur in type-checked program")
            }
          case PSymOp.ArithDiv => Div(l, r)(pos, info)
          case PSymOp.Mod => Mod(l, r)(pos, info)
          case PSymOp.Lt =>
            l.typ match {
              case Int => LtCmp(l, r)(pos, info)
              case Perm => PermLtCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case PSymOp.Le =>
            l.typ match {
              case Int => LeCmp(l, r)(pos, info)
              case Perm => PermLeCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case PSymOp.Gt =>
            l.typ match {
              case Int => GtCmp(l, r)(pos, info)
              case Perm => PermGtCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type " + l.typ.toString())
            }
          case PSymOp.Ge =>
            l.typ match {
              case Int => GeCmp(l, r)(pos, info)
              case Perm => PermGeCmp(l, r)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case PSymOp.EqEq => EqCmp(l, r)(pos, info)
          case PSymOp.Ne => NeCmp(l, r)(pos, info)
          case PSymOp.Implies => Implies(l, r)(pos, info)
          case PSymOp.Wand => MagicWand(l, r)(pos, info)
          case PSymOp.Iff => EqCmp(l, r)(pos, info)
          case PSymOp.AndAnd => And(l, r)(pos, info)
          case PSymOp.OrOr => Or(l, r)(pos, info)

          case PKwOp.In => right.typ match {
            case _: PSeqType => SeqContains(l, r)(pos, info)
            case _: PMapType => MapContains(l, r)(pos, info)
            case _: PSetType | _: PMultisetType => AnySetContains(l, r)(pos, info)
            case t => sys.error(s"unexpected type $t")
          }

          case PSymOp.Append => SeqAppend(l, r)(pos, info)
          case PKwOp.Subset => AnySetSubset(l, r)(pos, info)
          case PKwOp.Intersection => AnySetIntersection(l, r)(pos, info)
          case PKwOp.Union => AnySetUnion(l, r)(pos, info)
          case PKwOp.Setminus => AnySetMinus(l, r)(pos, info)
          case _ => sys.error(s"unexpected operator $op")
        }
      case PUnExp(op, pe) =>
        val e = exp(pe)
        op.rs match {
          case PSymOp.Neg =>
            e.typ match {
              case Int => Minus(e)(pos, info)
              case Perm => PermMinus(e)(pos, info)
              case _ => sys.error("unexpected type")
            }
          case PSymOp.Not => Not(e)(pos, info)
        }
      case PInhaleExhaleExp(_, in, _, ex, _) =>
        InhaleExhaleExp(exp(in), exp(ex))(pos, info)
      case PIntLit(i) =>
        IntLit(i)(pos, info)
      case p@PResultLit(_) =>
        // find function
        val func = p.getAncestor[PFunction].get
        Result(ttyp(func.typ.resultType))(pos, info)
      case bool: PBoolLit =>
        if (bool.b) TrueLit()(pos, info) else FalseLit()(pos, info)
      case PNullLit(_) =>
        NullLit()(pos, info)
      case p@PPredCall(name, params, callArgs) => {
        val mappedArgs = callArgs.inner.toSeq.map(e => exp(e))
        val convName = s"${name.name}${
          encodeTypeListAsString(
            params.map(v => v.inner.toSeq)
              .map(v => v.map(ttyp))
              .getOrElse(Nil))
        }"
        //        println(s"CONV NAME: ${convName}")
        PredicateAccess(mappedArgs, convName)(pos = p.pos._1, info = NoInfo, errT = NoTrafos)
      }
      case PFieldAccess(rcv, _, idn) => {
        if (isDatatype(rcv.typ)) {
          val translatedType = ttyp(rcv.typ)
          instantiateDatatypeTemplate(translatedType)
          //          println(s"FINDING DATATYPE FIELD FOR ACCESS: ${translatedType} -> ${idn.name}")
          FieldAccess(exp(rcv), findDatatypeField(translatedType, idn))(pos, info)
        }
        else {
          // TODO CFG: select the field with the given type associated :)
          //          println(s"FINDING FIELD: ${rcv.typ} -> ${idn.name}")
          FieldAccess(exp(rcv), findField(idn))(pos, info)
        }
      }
      case PMagicWandExp(left, _, right) => MagicWand(exp(left), exp(right))(pos, info)
      case pfa@PCall(func, args, _) =>
        members(func.name) match {
          case f: Function => FuncApp(f, args.inner.toSeq map exp)(pos, info)
          case f@DomainFunc(_, _, _, _, _) =>
            val actualArgs = args.inner.toSeq map exp
            /* TODO: Not used - problem?*/
            type TypeSubstitution = Map[TypeVar, Type]
            val so: Option[TypeSubstitution] = pfa.domainSubstitution match {
              case Some(ps) => Some(ps.m.map(kv => TypeVar(kv._1) -> ttyp(kv._2)))
              case None => None
            }
            so match {
              case Some(s) =>
                val d = members(f.domainName).asInstanceOf[Domain]
                assert(s.keys.toSet.subsetOf(d.typVars.toSet))
                val sp = s //completeWithDefault(d.typVars,s)
                assert(sp.keys.toSet == d.typVars.toSet)
                if (f.interpretation.isDefined)
                  BackendFuncApp(f, actualArgs)(pos, info)
                else
                  DomainFuncApp(f, actualArgs, sp)(pos, info)
              case _ => sys.error("type unification error - should report and not crash")
            }
          case _: Predicate =>
            val inner = PredicateAccess(args.inner.toSeq map exp, findPredicate(func).name)(pos, info)
            PredicateAccessPredicate(inner, None)(pos, info)
          case _ => sys.error("unexpected reference to non-function")
        }
      case PNewExp(_, _) => sys.error("unexpected `new` expression")
      case PUnfolding(_, loc, _, e) =>
        Unfolding(exp(loc).asInstanceOf[PredicateAccessPredicate], exp(e))(pos, info)
      case PApplying(_, wand, _, e) =>
        Applying(exp(wand).asInstanceOf[MagicWand], exp(e))(pos, info)
      case PAsserting(_, a, _, e) =>
        Asserting(exp(a), exp(e))(pos, info)
      case pl@PLet(_, _, _, exp1, _, PLetNestedScope(body)) =>
        Let(liftLogicalDecl(pl.decl), exp(exp1.inner), exp(body))(pos, info)
      case _: PLetNestedScope =>
        sys.error("unexpected node PLetNestedScope, should only occur as a direct child of PLet nodes")
      case PExists(_, vars, _, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp.inner.toSeq map exp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        Exists(vars.toSeq map liftLogicalDecl, ts, exp(e))(pos, info)
      case PForall(_, vars, _, triggers, e) =>
        val ts = triggers map (t => Trigger((t.exp.inner.toSeq map exp) map (e => e match {
          case PredicateAccessPredicate(inner, _) => inner
          case _ => e
        }))(t))
        val fa = Forall(vars.toSeq map liftLogicalDecl, ts, exp(e))(pos, info)
        if (fa.isPure) {
          fa
        } else {
          val desugaredForalls = QuantifiedPermissions.desugarSourceQuantifiedPermissionSyntax(fa)
          desugaredForalls.tail.foldLeft(desugaredForalls.head: Exp)((conjuncts, forall) =>
            And(conjuncts, forall)(fa.pos, fa.info, fa.errT))
        }
      case fp@PForPerm(_, vars, _, _, e) =>
        val varList = vars.toSeq map liftLogicalDecl
        exp(fp.accessRes) match {
          case PredicateAccessPredicate(inner, _) => ForPerm(varList, inner, exp(e))(pos, info)
          case f: FieldAccess => ForPerm(varList, f, exp(e))(pos, info)
          case p: PredicateAccess => ForPerm(varList, p, exp(e))(pos, info)
          case w: MagicWand => ForPerm(varList, w, exp(e))(pos, info)
          case other =>
            sys.error(s"Internal Error: Unexpectedly found $other in forperm")
        }
      case POldExp(_, lbl, e) =>
        val ee = exp(e.inner)
        lbl.map(l => LabelledOld(ee, l.inner.fold(_.rs.keyword, _.name))(pos, info)).getOrElse(Old(ee)(pos, info))
      case PCondExp(cond, _, thn, _, els) =>
        CondExp(exp(cond), exp(thn), exp(els))(pos, info)
      case PCurPerm(_, res) =>
        exp(res.inner) match {
          case PredicateAccessPredicate(inner, _) => CurrentPerm(inner)(pos, info)
          case x: FieldAccess => CurrentPerm(x)(pos, info)
          case x: PredicateAccess => CurrentPerm(x)(pos, info)
          case x: MagicWand => CurrentPerm(x)(pos, info)
          case other => sys.error(s"Unexpectedly found $other")
        }
      case PNoPerm(_) =>
        NoPerm()(pos, info)
      case PFullPerm(_) =>
        FullPerm()(pos, info)
      case PWildcard(_) =>
        WildcardPerm()(pos, info)
      case PEpsilon(_) =>
        EpsilonPerm()(pos, info)
      case acc: PAccPred =>
        val p = acc.permExp.map(exp)
        exp(acc.loc) match {
          case loc@FieldAccess(_, _) =>
            FieldAccessPredicate(loc, p)(pos, info)
          case loc@PredicateAccess(_, _) =>
            PredicateAccessPredicate(loc, p)(pos, info)
          case PredicateAccessPredicate(inner, _) => PredicateAccessPredicate(inner, p)(pos, info)
          case _ =>
            sys.error("unexpected location")
        }
      case _: PEmptySeq =>
        EmptySeq(ttyp(pexp.typ.asInstanceOf[PSeqType].elementType.inner))(pos, info)
      case PExplicitSeq(_, elems) =>
        ExplicitSeq(elems.inner.toSeq map exp)(pos, info)
      case PRangeSeq(_, low, _, high, _) =>
        RangeSeq(exp(low), exp(high))(pos, info)

      case PLookup(base, _, index, _) => base.typ match {
        case _: PSeqType => SeqIndex(exp(base), exp(index))(pos, info)
        case _: PMapType => MapLookup(exp(base), exp(index))(pos, info)
        case t => sys.error(s"unexpected type $t")
      }

      case PSeqSlice(seq, _, s, _, e, _) =>
        val es = exp(seq)
        val ss = e.map(exp).map(SeqTake(es, _)(pos, info)).getOrElse(es)
        s.map(exp).map(SeqDrop(ss, _)(pos, info)).getOrElse(ss)

      case PUpdate(base, _, key, _, value, _) => base.typ match {
        case _: PSeqType => SeqUpdate(exp(base), exp(key), exp(value))(pos, info)
        case _: PMapType => MapUpdate(exp(base), exp(key), exp(value))(pos, info)
        case t => sys.error(s"unexpected type $t")
      }

      case PSize(_, base, _) => base.typ match {
        case _: PSeqType => SeqLength(exp(base))(pos, info)
        case _: PMapType => MapCardinality(exp(base))(pos, info)
        case _: PSetType | _: PMultisetType => AnySetCardinality(exp(base))(pos, info)
        case t => sys.error(s"unexpected type $t")
      }

      case _: PEmptySet =>
        EmptySet(ttyp(pexp.typ.asInstanceOf[PSetType].elementType.inner))(pos, info)
      case PExplicitSet(_, elems) =>
        ExplicitSet(elems.inner.toSeq map exp)(pos, info)
      case _: PEmptyMultiset =>
        EmptyMultiset(ttyp(pexp.typ.asInstanceOf[PMultisetType].elementType.inner))(pos, info)
      case PExplicitMultiset(_, elems) =>
        ExplicitMultiset(elems.inner.toSeq map exp)(pos, info)

      case _: PEmptyMap => EmptyMap(
        ttyp(pexp.typ.asInstanceOf[PMapType].keyType),
        ttyp(pexp.typ.asInstanceOf[PMapType].valueType)
      )(pos, info)
      case PExplicitMap(_, elems) =>
        ExplicitMap(elems.inner.toSeq map exp)(pos, info)
      case PMaplet(key, _, value) =>
        Maplet(exp(key), exp(value))(pos, info)
      case PMapDomain(_, base) =>
        MapDomain(exp(base.inner))(pos, info)
      case PMapRange(_, base) =>
        MapRange(exp(base.inner))(pos, info)

      case t: PExtender => t.translateExp(this)
    }
  }

  implicit def liftPos(node: Where): SourcePosition = Translator.liftWhere(node)

  /** Takes a `PAnyFormalArgDecl` and turns it into a `AnyLocalVarDecl`. */
  def liftAnyArgDecl(formal: PAnyFormalArgDecl) =
    formal match {
      case f: PFormalArgDecl => liftArgDecl(f)
      case PDomainFunctionArg(Some(idndef), _, typ) => LocalVarDecl(idndef.name, ttyp(typ))(idndef)
      case PDomainFunctionArg(None, _, typ) => UnnamedLocalVarDecl(ttyp(typ))(typ)
    }

  /** Takes a `PFormalArgDecl` and turns it into a `LocalVarDecl`. */
  def liftArgDecl(formal: PFormalArgDecl) =
    LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(pos = formal.idndef, info = SourcePNodeInfo(formal))

  /** Takes a `PFormalReturnDecl` and turns it into a `LocalVarDecl`. */
  def liftReturnDecl(formal: PFormalReturnDecl) =
    LocalVarDecl(formal.idndef.name, ttyp(formal.typ))(pos = formal.idndef, info = SourcePNodeInfo(formal))

  /** Takes a `PLogicalVarDecl` and turns it into a `LocalVarDecl`. */
  def liftLogicalDecl(logical: PLogicalVarDecl) =
    LocalVarDecl(logical.idndef.name, ttyp(logical.typ))(pos = logical.idndef, info = SourcePNodeInfo(logical))

  /** Takes a `PType` and turns it into a `Type`. */
  def ttyp(t: PType): Type = {
    t match {
      case PPrimitiv(name) => name.rs match {
        case PKw.Int => Int
        case PKw.Bool => Bool
        case PKw.Ref => Ref
        case PKw.Perm => Perm
        case PKw.Rational => Perm
      }
      case PSeqType(_, elemType) =>
        SeqType(ttyp(elemType.inner))
      case PSetType(_, elemType) =>
        SetType(ttyp(elemType.inner))
      case PMultisetType(_, elemType) =>
        MultisetType(ttyp(elemType.inner))
      case typ: PMapType =>
        MapType(ttyp(typ.keyType), ttyp(typ.valueType))
      case typ@PDomainType(name, args) =>
        if (isDatatype(name.name)) {
          // TODO CFG: recognize datatype, maybe do the instantiation here?!
          val temp = getGenericParameterInfo(name.name)
          val vars = temp.map(g => TypeVar(g))
          val mapped = args.map(v => v.inner.toSeq).getOrElse(Nil).map(a => ttyp(a))
          DatatypeType(name.name, vars.zip(mapped).toMap)(vars)
        }
        else {
          members.get(name.name) match {
            case Some(domain: Domain) =>
              if (domain.interpretations.isDefined) {
                BackendType(domain.name, domain.interpretations.get)
              } else {
                val typVarMapping = domain.typVars zip (typ.typeArgs map ttyp)
                DomainType(domain, typVarMapping /*.filter {
            case (tv, tt) => tv!=tt //!tt.isInstanceOf[TypeVar]
          }*/.toMap)
              }
            case Some(adt: Adt) =>
              val typVarMapping = adt.typVars zip (typ.typeArgs map ttyp)
              AdtType(adt, typVarMapping.toMap)
            case Some(other) =>
              sys.error(s"Did not expect member ${other}")
            case None =>
              assert(typ.typeArgs.isEmpty)
              TypeVar(name.name) // not a domain, i.e. it must be a type variable
          }
        }
      case TypeHelper.Wand => Wand
      case TypeHelper.Predicate => Bool
      case TypeHelper.Impure => Bool
      case t: PExtender => t.translateType(this)
      case PUnknown() =>
        sys.error("unknown type unexpected here")
      case _: PFunctionType =>
        sys.error("unexpected use of internal typ")

    }
  }
}

object Translator {

  import scala.annotation.unused

  /** Takes a [[viper.silver.parser.FastPositioned]] and turns it into a [[viper.silver.ast.SourcePosition]]. */
  implicit def liftWhere(node: Where): SourcePosition = {
    if (node.pos._1.isInstanceOf[FilePosition]) {
      assert(node.pos._2.isInstanceOf[FilePosition])

      val begin = node.pos._1.asInstanceOf[FilePosition]
      val end = node.pos._2.asInstanceOf[FilePosition]

      SourcePosition(begin.file,
        LineColumnPosition(begin.line, begin.column),
        LineColumnPosition(end.line, end.column))
    }
    else {
      SourcePosition(null, 0, 0)
    }
  }

  def toInfo(annotations: Seq[PAnnotation], @unused node: PNode): Info = {
    if (annotations.isEmpty) {
      NoInfo
    } else {
      AnnotationInfo(annotations.groupBy(_.key).map { case (k, v) => k.str -> v.flatMap(_.values.inner.toSeq.map(_.str)) })
    }
  }
}
