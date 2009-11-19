object p {
  import synthesis.Definitions._

  def main(args: Array[String]) : Unit = {
    val x = 3

    val y = 9

    y match {
      case `x` * 3 + 1 => println("true" + x)
      case _ => println("false" )
    }
  }
}

