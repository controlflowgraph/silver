package viper.silver.inference.v3

import viper.silver.inference.v3.ast.{BaguetteMagic, MapTermSub}

case class MagicWandManager(wands: Set[BaguetteMagic]) {

  def this() = {
    this(Set())
  }

  def addWand(wand: BaguetteMagic): MagicWandManager = {
    MagicWandManager(this.wands.union(Set(wand)))
  }

  def removeWand(wand: BaguetteMagic): MagicWandManager = {
    MagicWandManager(this.wands.diff(Set(wand)))
  }

  def substitute(ts: MapTermSub): MagicWandManager = {
    MagicWandManager(this.wands.map(w => w.substitute(ts).asInstanceOf[BaguetteMagic]))
  }

  def pretty(): String = {
    this.wands.map(m => m.pretty()).mkString("\n")
  }
}