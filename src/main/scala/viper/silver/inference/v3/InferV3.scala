package viper.silver.inference.v3

import viper.silver.ast.Program
import viper.silver.inference.v3.ast.{InternalRepresentation, PredDef}

case class InferV3(program: Program) {



  def process(): Option[Program] = {
    this.program.methods.foreach(m => {
      val rep = new InternalRepresentation()
      val prev = Set(rep.freshIdent())
      val defs: Map[String, PredDef] = Map()
      InternalFormTranslator.transformSeqnToInternalForm(rep, prev, defs, m.bodyOrAssumeFalse, None)

      println(rep.pretty())
    })
    None
  }
}
