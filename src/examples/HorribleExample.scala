import synthesis.Definitions._

object ScaleWeights {
  def main(args: Array[String]): Unit = {
    println("Give me the total and the three limits K P Q to find a, b, c and d")
    println("such that a + 17b + 295c + 5124d == total and a, b, c are bounded by K, P, Q on the right respectively")
    val total: Int = Console.readInt
    val limit1: Int = Console.readInt
    val limit2: Int = Console.readInt
    val limit3: Int = Console.readInt

    try {
      val (a, b, c, d) = choose((a:Int,b:Int,c:Int,d:Int) => (
           a + 17 * b + 295 * c + 5124 * d == total
        && 0 <= a && a <= limit1
        && 0 <= b && b <= limit2
        && 0 <= c && c <= limit3
      ))
      println(a+" + 17*"+b+" + 295*"+c+" + 5124*"+d+" = "+total)
    } catch {
      case UnsatisfiableConstraint() => println("Sorry, there are no such decomposition with the imposed upper bounds. Try higher upper bounds ?")
    }
  }
}
