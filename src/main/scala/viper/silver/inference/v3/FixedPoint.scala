package viper.silver.inference.v3

object FixedPoint {
  def compute[T](start: T, f: T => T): T = {
    val applied = f(start)
    if (start.equals(applied)) {
      start
    }
    else {
      compute(applied, f)
    }
  }
}