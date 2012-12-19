import synthesis.Definitions._

object BarbaraBrokeIt {
   def main(args: Array[String]): Unit = {
     println("Give me a lower bound [0-100]: ")
     val lower: Int = Console.readInt
     println("Give me an upper bound [0-100]: ")
     val upper: Int = Console.readInt
     try {
       val (x,y,g) = choose(
     (x:Int,y:Int,g:Int) => (
     18*g == 3*x + 2*y &&
          x > 0 && y > 0 &&
     lower <= g && g <= upper
      ));
     println("x: " + x)
     println("y: " + y)
     println("G: " + g)
     } catch {
       case UnsatisfiableConstraint() => println("Sorry, no solution")
     }
   }
}
