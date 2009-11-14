import synthesis.Definitions._

object Minimal {
  def main(args: Array[String]): Unit = {
    val x = Console.readInt
    val y = Console.readInt
    val z = choose((z:Int) => z > x && z < y)
    println(x + " < " + z + " < " + y)

  }
}
