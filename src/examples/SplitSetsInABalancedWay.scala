import synthesis.Definitions._
import scala.collection.immutable.Set

object SplitSetsInABalancedWay {
  def main(args : Array[String]) : Unit = {

    val bigSet = Set("Ladybugs", "must", "render", "you", "catatonic", ".")

//    val z = Set.empty[String]
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
