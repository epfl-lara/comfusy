import synthesis.Definitions._

object ProducesIF {
  def main(args : Array[String]) : Unit = {
    println("Give me a number N, and I'll try to find you x,y,z such that:")
    println("x >= 0 && y - x >= 0 && z >= 0 && y - z >= 0 && ((3 * y) - (2 * z) + x) == N")
    val b = Console.readInt 

    try {
      val (x,y,z) = choose((x:Int,y:Int,z:Int) => {
        x >= 0 && y - x >= 0 && z >= 0 && y - z >= 0 && ((3 * y) - (2 * z) + x) - b == 0
      })
      println("x: " + x + ", y: " + y + ", z: " + z)
    } catch {
      case UnsatisfiableConstraint() => println("Sorry, couldn't do it.")
    }
  }
}
