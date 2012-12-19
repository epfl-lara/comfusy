import synthesis.Definitions._

object ImplicitExtractors {
  def main(args: Array[String]): Unit = {
    println("Give me a prime number.")
    val n = Console.readInt

    val 6 * x + 1 = n 
    println(x + "*6 + 1 = " + n)
  }
}
