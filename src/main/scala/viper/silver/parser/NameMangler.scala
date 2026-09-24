package viper.silver.parser

import viper.silver.ast.{AtomicType, BackendType, Bool, BuiltInType, CollectionType, DatatypeType, Domain, DomainType, ExtensionType, GenericType, InferInfo, Int, InternalType, MapType, MultisetType, Perm, Ref, SeqType, SetType, Type, TypeVar, Wand}

case class NameMangler(inferInfo: InferInfo) {
  def getDatatype(name: String): DatatypeTemplate = {
    inferInfo.datatypeTemplates(name)
  }

  def getDomain(name: String): Domain = {
    inferInfo.domains(name)
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

  def encodeTypeListAsString(typ: Seq[Type]): String = {
    if (typ.isEmpty) ""
    else {
      val joined = typ.map(encodeTypeAsString)
        .reduceOption((a, b) => a + "$$$_" + b)
        .getOrElse("")
      s"${"$$_"}${joined}${"$$$$_"}"
    }
  }

}
