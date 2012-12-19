import synthesis.Definitions._

object PatternMatching {
  def main(args: Array[String]): Unit = {
    println("Give me a number.")
    val n = Console.readInt

    val str = n match {
      case 3 * k     => n + " is 3 * " + k
      case 3 * k + 1 => n + " is 3 * " + k + " + 1"
      case 3 * k + 2 => n + " is 3 * " + k + " + 2"
    }
    println(str)
  }
}
