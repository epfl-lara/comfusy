import synthesis.Definitions._

object ImpossibleConstraints {
  def main(args : Array[String]) : Unit = {
    val x = choose((x: Int) => x >= 0 && 2*x < x)
    println("...and the non-existant number is: " + x)
  }
}
