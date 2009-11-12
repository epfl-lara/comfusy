import synthesis.Definitions._

object Minimal {
  def main(args: Array[String]): Unit = {
    val y: Int = 4
    val z = 5
    val x = choose((x: Int) => (5*(x-y) <= 2 && x > 4))
    println(x)
  }
}
