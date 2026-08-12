package viper.silver.inference.v3

case class Counter(var value: Int) {
  def next(): Int = {
    val v = this.value
    this.value += 1
    v
  }
}