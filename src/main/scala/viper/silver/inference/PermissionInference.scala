package viper.silver.inference

import viper.silver.ast._
import viper.silver.inference.v1.PermInf
import viper.silver.inference.v2.Infer


object PermissionInference {
  def process(program: Program): Option[Program] = {
    try{
      Infer(program).process()
    }
    catch {
      case e: Exception => {
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
        println(e.toString)
        e.getStackTrace.toList.take(100).foreach(println)
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
        println("::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
        throw new IllegalStateException("AHHH")
      }
    }
  }
}