package viper.silver.inference

import viper.silver.ast._
import viper.silver.inference.v1.PermInf
import viper.silver.inference.v2.Infer
import viper.silver.inference.v3.InferV3
import viper.silver.verifier.{VerificationResult, Verifier}


object PermissionInference {
  def process(program: Program, verifier: Verifier): Option[Program] = {
    try{
//      Infer(program).process()
      InferV3(program, verifier).process()
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

// TODO: example that creates a list of the first n numbers
// TODO: allow assume only with pure information -> put into documentation
// TODO: maybe use viper to prove something
//       -> check if entailment proof can show that an unfolding strategy is able to