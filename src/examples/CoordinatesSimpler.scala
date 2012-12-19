import synthesis.Definitions._

object CoordinatesSimpler {
  def main(args : Array[String]) : Unit = {
    println("Size X ?")
    val x = Console.readInt
    println("Size Y ?")
    val y = Console.readInt

    println("Index ?")
    val i = Console.readInt

    val (j, k) = choose((j: Int, k: Int) => ( 
         i == k * x + j )
      && 0 <= j && j < x
      && 0 <= k && k < y
    )

    println("Index " + i + " corresponds to coordinate (" + j + ", " + k + ") in the space.")
  }
}
