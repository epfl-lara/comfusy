import synthesis.Definitions._

object GeneratesLoops {
  def main(args: Array[String]) : Unit = {
    val a = 42
    val b = 12
    val c = -7

    val (x,y,z) = choose((x: Int, y: Int, z: Int) => (c - y <= a - x*6 && a - x*6 <= b + x + y*7  &&  x > y + z && z*9 <= x+y && z*5 > b + x + 8))

    println("x: " + x)
    println("y: " + y)
    println("z: " + z)
  }
}
