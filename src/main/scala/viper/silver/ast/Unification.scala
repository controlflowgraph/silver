package viper.silver.ast

import viper.silver.FastMessaging
import viper.silver.parser.{PBoolImpureType, PBoolPredicateType, PBoolWandType, PDomainType, PDomainTypeKinds, PFunctionType, PMacroType, PMapType, PMultisetType, PNode, PPrimitiv, PSeqType, PSetType, PType, PUnknown}

object Unification {
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

  def findUnificationForPair(error: PNode => String => Unit, call: PNode, arg: PType, value: PType): Option[Map[String, PType]] = {
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
            .map(v => findUnificationForPair(error, call, v._1, v._2))
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
        val res1 = findUnificationForPair(error, call, t1.inner.first, t2.inner.first)
        val res2 = findUnificationForPair(error, call, t1.inner.second, t2.inner.second)
        (res1, res2) match {
          case (Some(v1), Some(v2)) => mergeUnificationResults(v1, v2)
          case _ => None
        }
      case (PMultisetType(_, elem1), PMultisetType(_, elem2)) => findUnificationForPair(error, call, elem1.inner, elem2.inner)
      case (PPrimitiv(n1), PPrimitiv(n2)) => if (n1.rs.equals(n2.rs)) {
        Some(Map())
      } else {
        None
      }
      case (PSeqType(_, elem1), PSeqType(_, elem2)) => findUnificationForPair(error, call, elem1.inner, elem2.inner)
      case (PSetType(_, elem1), PSetType(_, elem2)) => findUnificationForPair(error, call, elem1.inner, elem2.inner)
      // TODO: add case for generic parameter and every other type
      case (d1@PDomainType(dom1, _), d2) if d1.kind == PDomainTypeKinds.TypeVar =>
        // TODO: set the substitution
        Some(Seq((dom1.name, d2)).toMap)
      case (d1@PDomainType(dom1, args1), d2@PDomainType(dom2, args2)) =>
        val mappedArgs1 = args1.map(_.inner.toSeq).getOrElse(Nil)
        val mappedArgs2 = args2.map(_.inner.toSeq).getOrElse(Nil)
        if (d1.kind == d2.kind && dom1.name.equals(dom2.name) && mappedArgs1.length == mappedArgs2.length) {
          mappedArgs1.zip(mappedArgs2)
            .map(v => findUnificationForPair(error, call, v._1, v._2))
            .foldLeft[Option[Map[String, PType]]](Some(Map()))((acc, v) => (acc, v) match {
              case (Some(m1), Some(m2)) => mergeUnificationResults(m1, m2)
              case _ => None
            })
        }
        else {
          None
        }
      case _ => {
        error(call)(s"failed unification of `${arg}` and `${value}`")
        None
      }
    }
  }

  def findUnificationForArgs(error: PNode => String => Unit, call: PNode, argPairs: Seq[(PType, PType)]): Option[Map[String, PType]] = {
    val result = argPairs.map(p => (p, findUnificationForPair(error, call, p._1, p._2)))
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
                    error(call)(s"incompatible generic parameter instantiations `$typ` and `${value(k)}` (originating from: `${rr._1._1}` and `${rr._1._2}`)")
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
}
