import synthesis.Definitions._
import scala.collection.immutable.Set

object SetConstraints {
  def main(args : Array[String]) : Unit = {

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
}

