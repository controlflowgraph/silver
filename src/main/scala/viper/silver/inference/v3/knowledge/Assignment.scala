package viper.silver.inference.v3.knowledge

import viper.silver.ast.Type
import viper.silver.inference.v3.{RefCounter, ValRef}

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