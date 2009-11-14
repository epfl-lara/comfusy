import synthesis.Definitions._

object Minimal {
  def main(args: Array[String]): Unit = {
    val x = 14
    val y = 16
    val z = choose((z:Int) => z > x && z < y)
    println(x)
    println(y)


  }
}
