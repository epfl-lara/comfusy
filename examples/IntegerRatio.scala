import synthesis.Definitions._

object IntegerRatio {
    def main(args : Array[String]) : Unit = {
        println("a ? ")
        val a = Console.readInt
        println("b ? ")
        val b = Console.readInt
        try {
          val x = choose((x: Int) => a * x == b || b * x == a)
          println("Ratio is " + x)
        } catch {
          case UnsatisfiableConstraint() => println("Couldn't find an integer ratio between 'a' and 'b'.")
        }
    }
}
