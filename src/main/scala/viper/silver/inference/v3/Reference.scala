package viper.silver.inference.v3

import viper.silver.ast.Type
import viper.silver.inference.v3.ast.VarTerm

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


case class RefCounter(counter: Counter) {
  def freshValRef(): ValRef = {
    ValRef(this.counter.next())
  }
}
