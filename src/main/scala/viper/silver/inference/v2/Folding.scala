package viper.silver.inference.v2

case class FoldingStep(unfolding: Boolean, pred: PredInstance) {

}

case class FoldingStrategy(steps: Seq[FoldingStep]) {
  def merge(other: FoldingStrategy): FoldingStrategy = {
    FoldingStrategy((steps ++ other.steps).foldLeft((Set[FoldingStep](), Seq[FoldingStep]()))((acc, step) => {
      if (acc._1.contains(step)) {
        acc
      }
      else {
        (acc._1.union(Set(step)), acc._2 ++ Seq(step))
      }
    })._2)
  }

  def pretty(): String = {
    this.steps.map(s => (if (s.unfolding) "unfold " else "fold   ") + s.pred.pretty()).mkString("\n")
  }
}