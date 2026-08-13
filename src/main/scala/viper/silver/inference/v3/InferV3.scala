package viper.silver.inference.v3

import viper.silver.ast.Program
import viper.silver.inference.v3.ast.{CallLine, FieldAssignLine, InternalMethod, PredDef}

case class InferV3(program: Program) {

  private def transformMethodsToInternalRepresentation(defs: Map[String, PredDef]): Map[String, InternalMethod] = {
    this.program.methods.map(m => {
      val res = InternalFormTranslator.processToInternalForm(defs, m)
      println(res.rep.pretty())
      res.method -> res
    }).toMap
  }

  def process(): Option[Program] = {

    println("------------------ PROCESSING ------------------")
    val defs = PredDefExtractor.extractPredDefs(this.program)
    println("pred definitions:")
    defs.foreach(d => println(s"${d._1}: ${d._2.pretty()}"))

    println("------------------")

    val reps = transformMethodsToInternalRepresentation(defs)

    Inference(defs, reps, this.program).infer()

    None
  }
}
