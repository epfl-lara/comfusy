import synthesis.Definitions._

object Minimal {
  def main(args: Array[String]): Unit = {
    val y = 4
    val z = 5
    val x = choose((x: Int) => (y==z))
    println(x)
  }
}
