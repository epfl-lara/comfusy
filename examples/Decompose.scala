import synthesis.Definitions._

object Decompose {
  def main(args : Array[String]) : Unit = {
    Console.println("Give me a number, please.")
    val n = Console.readInt

    val 2 * x + 3 * y = n

    println("Did you know that " + n + " can be written as 2*" + x + " + 3*" + y + " ?")
  }
}
