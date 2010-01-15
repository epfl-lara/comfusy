import synthesis.Definitions._

object RequiresParametrizedArith {
  def main(args : Array[String]) : Unit = {
    val a = 42
    val b = 31

    val (x,y) = choose((x: Int, y: Int) => (a * x + a * a * b * b * y == 51))

    println("a : " + a)
    println("b : " + b)
    println("x : " + x)
    println("y : " + y)
  }
}
