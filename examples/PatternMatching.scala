import synthesis.Definitions._

object PatternMatching {
  def main(args: Array[String]): Unit = {
    println("Give me a number.")
    val n = Console.readInt

    n match {
      case 3 * k     => println(n + " is 3 * " + k)
      case 3 * k + 1 => println(n + " is 3 * " + k + " + 1")
      case 3 * k + 2 => println(n + " is 3 * " + k + " + 2")
    }
  }
}
