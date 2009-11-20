import synthesis.Definitions._

object PrimeHeuristic {
  def maybePrime(n: Int): Boolean = n match {
    case 2 * k     => false
    case 3 * k     => false
    case 6 * k - 1 => true
//    case 6 * k + 1 => true
  }

  def main(args : Array[String]) : Unit = {
    println("Number !")
    val x = Console.readInt

    println("Any chance that " + x + " is prime ? " + maybePrime(x))
  }
}
