import synthesis.Definitions._
import scala.collection.immutable.Set

object All {
  def main(args : Array[String]) : Unit = {
    m1
    m2
    m3
    m4
    m5
    m6
  }

  def pow(base: Int, p: Int) = {
    def fp(m : Int, b : Int, i : Int) : Int = i match {
      case 0         => m
      case 2 * j     => fp(m, b*b, j)
      case 2 * j + 1 => fp(m*b, b*b, j)
    }
    fp(1, base, p)
  }

  def m1: Unit = {
    println("Base ?")
    val bse = Console.readInt
    println("Exponent ?")
    val exp = Console.readInt
    println(bse + "^" + exp + " = " + pow(bse,exp))
  }

  def maybePrime(n: Int): Boolean = n match {
    case 2 * k     => false
    case 3 * k     => false
    case 6 * k - 1 => true
    case 6 * k + 1 => true
  }

  def m2: Unit = {
    println("Number !")
    val x = Console.readInt

    println("Any chance that " + x + " is prime ? " + maybePrime(x))
  }

  def m3: Unit = {
    println("Give me a weight: ")
    val weight: Int = Console.readInt

    try {
      val (w1,w2,w3,w4) = choose((w1:Int,w2:Int,w3:Int,w4:Int) => (
           w1 + 3 * w2 + 9 * w3 + 27 * w4 == weight
        && -1 <= w1 && w1 <= 1
        && -1 <= w2 && w2 <= 1
        && -1 <= w3 && w3 <= 1
        && -1 <= w4 && w4 <= 1
      ))
      println("Put what you think weights " + weight + " to the left, then")
      println("Put 1         : " + numToPlace(w1))
      println("Put 3         : " + numToPlace(w2))
      println("Put 9         : " + numToPlace(w3))
      println("Put 27        : " + numToPlace(w4))
    } catch {
      case UnsatisfiableConstraint() => println("Sorry, cannot measure " + weight + " with weights 1,3,9 and 27.")
    }
  }

  def numToPlace(i: Int): String = i match {
    case -1 => "to the left"
    case  0 => "nowhere"
    case  1 => "to the right"
    case  _ => "??? " + i
  }

  def m4: Unit = {
    println("Please enter a number of seconds: ")
    val secnum: Int = Console.readInt

    val (hours, minutes, seconds) = choose((h: Int, m: Int, s: Int) => (
           h * 3600 + m * 60 + s == secnum
        && 0 <= m
        && m < 60
        && 0 <= s
        && s < 60
      ) )

    println(secnum + "s = " + hours + "h, " + minutes + "m and " + seconds + "s.")
  }

  def m5: Unit = {

    val bigSet = Set("AA", "BB", "CC", "DD", "EE")

    val setZ = Set.empty[String]
    val maxDiff = 1

    val (setA, setB) = choose((A: Set[String], B: Set[String]) => ( A ++ B == bigSet && A ** B == Set.empty && A.size > 0 && B.size > 0 ))

    println("We can split:")
    println(bigSet)
    println("...into:")
    println(setA)
    println("...and:")
    println(setB)
  }

  def m6: Unit = {

    val bigSet = Set("Ladybugs", "must", "render", "you", "catatonic", ".")

    val maxDiff = 1

    val (setA, setB) = choose((A: Set[String], B: Set[String]) => (
         -maxDiff <= A.size - B.size && A.size - B.size <= maxDiff
      && A ++ B == bigSet
      && A ** B == Set.empty
    ))

    println("We can split:")
    println(bigSet)
    println("...into:")
    println(setA)
    println("...and:")
    println(setB)
  }

}
