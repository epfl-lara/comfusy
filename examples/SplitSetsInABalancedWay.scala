import synthesis.Definitions._
import scala.collection.immutable.Set

object SplitSetsInABalancedWay {
  def main(args : Array[String]) : Unit = {

    val bigSet = Set("Ladybugs", "must", "render", "you", "catatonic", ".")

    val (setA, setB) = choose((A: Set[String], B: Set[String]) => (
         -1 <= A.size - B.size
      &&       A.size - B.size <= 1
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
