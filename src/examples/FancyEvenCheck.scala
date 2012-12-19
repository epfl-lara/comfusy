import synthesis.Definitions._

object FancyEvenCheck {
  def main(args : Array[String]) : Unit = {
    println("I like numbers, please give me one !")

    Console.readInt match {
      case 2 * _ => println("Your number can be divided by two.")
      case 3 * _ => println("Your number cannot be divided by two, but can be divided by three.")
      case _ => println("Your number is neither a multiple of two nor a multiple of three.")
    }
  }
}
