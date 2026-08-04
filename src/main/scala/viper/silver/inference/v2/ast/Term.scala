package viper.silver.inference.v2.ast

import viper.silver.ast.Type
import viper.silver.inference.v2.VariableInstantiation

trait Term {
  def substitute(es: TermSub) : Term

  def instantiate(init: VariableInstantiation) : Term

  def pretty() : String
}

case class IntTerm(value: BigInt, typ: Type) extends Term {

  def pretty() : String = this.value.toString()

  def substitute(es: TermSub): Term = {
    es.apply(this)
  }
  def instantiate(init: VariableInstantiation) : Term = {
    this
  }
}

case class BoolTerm(value: Boolean, typ: Type) extends Term {

  def pretty() : String = s"${this.value}"

  def substitute(es: TermSub): Term = {
    es.apply(this)
  }

  def instantiate(init: VariableInstantiation) : Term = {
    this
  }
}

case class NullTerm(typ: Type) extends Term {
  def pretty() : String = "null"

  def substitute(es: TermSub): Term = {
    es.apply(this)
  }

  def instantiate(init: VariableInstantiation) : Term = {
    this
  }
}

case class AddTerm(a: Term, b: Term, typ: Type) extends Term {
  def pretty() : String = s"${this.a.pretty()} + ${this.b.pretty()}"

  def substitute(es: TermSub): Term = {
    es.apply(AddTerm(
      this.a.substitute(es),
      this.b.substitute(es),
      this.typ
    ))
  }

  def instantiate(init: VariableInstantiation): AddTerm = {
    AddTerm(
      this.a.instantiate(init),
      this.b.instantiate(init),
      this.typ
    )
  }
}

case class SubTerm(a: Term, b: Term, typ: Type) extends Term {
  def pretty() : String = s"${this.a.pretty()} - ${this.b.pretty()}"

  def substitute(es: TermSub): Term = {
    es.apply(AddTerm(
      this.a.substitute(es),
      this.b.substitute(es),
      this.typ
    ))
  }

  def instantiate(init: VariableInstantiation): AddTerm = {
    AddTerm(
      this.a.instantiate(init),
      this.b.instantiate(init),
      this.typ
    )
  }
}

case class Var(name: String, typ: Type) extends Term {

  def pretty() : String = this.name

  def substitute(es: TermSub): Term = {
    es.apply(this)
  }

  def instantiate(init: VariableInstantiation): Term = {
    init.mapping.getOrElse(this.name, this)
  }
}

case class FieldAcc(v: Term, field: String, typ: Type) extends Term {

  def pretty() : String = s"${this.v.pretty()}.${this.field}"

  def instantiate(init: VariableInstantiation) : FieldAcc = {
    FieldAcc(this.v.instantiate(init), this.field, this.typ)
  }

  def substitute(es: TermSub): Term = {
    es.apply(FieldAcc(this.v.substitute(es), this.field, this.typ))
  }
}

case class FracPerm(left: Term, right: Term, typ: Type) extends Term {

  def pretty() : String = s"${this.left.pretty()} / ${this.right.pretty()}"

  def substitute(es: TermSub): Term = {
    es.apply(FracPerm(
      this.left.substitute(es),
      this.right.substitute(es),
      this.typ
    ))
  }

  def instantiate(init: VariableInstantiation): FracPerm = {
    FracPerm(
      this.left.instantiate(init),
      this.right.instantiate(init),
      this.typ
    )
  }
}