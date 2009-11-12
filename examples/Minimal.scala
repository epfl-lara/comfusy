import synthesis.Definitions._

object Minimal {
  def main(args: Array[String]): Unit = {
    val y: Int = 4
    val z = 5
    val x = choose((x: Int) => !(x % 3 != 4 || -(z+x+2) < 3 || !(y >= z)))
    println(x)
  }
}
