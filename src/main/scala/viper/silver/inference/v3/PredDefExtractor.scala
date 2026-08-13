package viper.silver.inference.v3

import viper.silver.ast.{Predicate, Program}
import viper.silver.inference.v3.ast.{BoolTerm, PredDef}

object PredDefExtractor {
  private def extractPredDef(pred: Predicate): PredDef = {
    PredDef(
      pred.name,
      pred.formalArgs.map(a => a.name),
      pred.body.map(b => InternalFormTranslator.expToLogicTerm(b)).getOrElse(BoolTerm(true))
    )
  }

  def extractPredDefs(program: Program): Map[String, PredDef] = {
    program.predicates.map(extractPredDef).map(d => d.name -> d).toMap
  }
}
