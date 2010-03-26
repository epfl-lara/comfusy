import synthesis.Definitions._

object Offset3D {
  def main(args : Array[String]) : Unit = {
    println("Offset?")
    val offset = Console.readInt

    println("Dim X?")
    val dimX = Console.readInt
    println("Dim Y?")
    val dimY = Console.readInt
    println("Dim Z?")
    val dimZ = Console.readInt

    val (x1, y1, z1) = choose((x: Int, y: Int, z: Int) => 
      offset == x + dimX * y + dimX * dimY * z &&
      0 <= x && x < dimX &&
      0 <= y && y < dimY &&
      0 <= z && z < dimZ)

    println("x : " + x1)
    println("y : " + y1)
    println("z : " + z1)
  }
}
