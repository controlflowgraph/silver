package viper.silver.inference.v3

import viper.silver.ast.Program
import viper.silver.inference.v3.ast.{InternalRepresentation, PredDef}

case class InferV3(program: Program) {



  def process(): Option[Program] = {

    println("------------------ PROCESSING ------------------")
    val defs = PredDefExtractor.extractPredDefs(this.program)
    println("pred definitions:")
    defs.foreach(d => println(s"${d._1}: ${d._2.pretty()}"))

    println("------------------")

    this.program.methods.foreach(m => {
      val rep = new InternalRepresentation()
      val prev = Set(rep.freshIdent())
      InternalFormTranslator.transformSeqnToInternalForm(rep, prev, defs, m.bodyOrAssumeFalse, None)

      println(rep.pretty())
    })
    None
  }
}
