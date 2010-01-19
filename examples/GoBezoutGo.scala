import synthesis.Definitions._

object GoBezoutGo {
  def main(args : Array[String]) : Unit = {
    Console.println("i + a*x + b*y + c*z == 0")
    Console.println("i?")
    val i = Console.readInt
    Console.println("a?")
    val a = Console.readInt
    Console.println("b?")
    val b = Console.readInt
    Console.println("c?")
    val c = Console.readInt

    val (x,y,z) = choose((x:Int, y:Int, z:Int) => (i + a*x + b*y + c*z == 0))

    println("x : " + x)
    println("y : " + y)
    println("z : " + z)
  }
}
