package viper.silver.inference.v3.knowledge

import viper.silver.inference.v3.{RefCounter, ValRef}

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
    val currentPretty = this.objMap.values
      .map(o => s"${o.ref.pretty()}:\n${
        o.fields.map(e => s"${e._1}: ${e._2.pretty()}")
          .mkString("\n")
          .indent(2)
      }"
        .indent(2))
      .mkString("\n")
    val refsPretty = s"{${this.initialized._1.map(v => v.pretty()).mkString(", ")}}"
    val initializedPretty = this.initialized._2.map(v => s"${v._1.pretty()}.${v._2}  =>  ${v._3.pretty()}").mkString("\n")
    s"current:\n${currentPretty.indent(2)}\ninitialized:\n${refsPretty.indent(2)}\n${initializedPretty.indent(2)}"
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