import synthesis.Definitions._

object ProducesIF {
  def main(args : Array[String]) : Unit = {
    val b = Console.readInt 

    val (x,y,z) = choose((x:Int,y:Int,z:Int) => {
      x >= 0 && y - x >= 0 && z >= 0 && y - z >= 0 && ((3 * y) - (2 * z) + x) - b == 0
    })

    println(x + " " + y + " " + z)
  }
}
