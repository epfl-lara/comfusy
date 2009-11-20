import synthesis.Definitions._

object FastExponentiation {
  def pow(base: Int, p: Int) = {
    def fp(m : Int, b : Int, i : Int) : Int = i match {
      case 0         => m
      case 2 * j     => fp(m, b*b, j)
      case 2 * j + 1 => fp(m*b, b*b, j)
    }
    fp(1, base, p)
  }

  def main(args : Array[String]) : Unit = {
    println("Base ?")
    val bse = Console.readInt
    println("Exponent ?")
    val exp = Console.readInt
    println(bse + "^" + exp + " = " + pow(bse,exp))
  }
}
