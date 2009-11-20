package synthesis

/** All definitions which are meant to be used ``as the library''.  */
object Definitions {
  /** This exception is thrown when the constraint-solving generated code can not solve the constraints. */
  case class UnsatisfiableConstraint() extends Exception("The constraints cannot be satisfied.")

  private def chooseNotRewritten: Nothing = error("``choose'' was not rewritten by the synthesis plugin")
  def choose[A](predicate: A => Boolean) : A = chooseNotRewritten
  def choose[A](predicate: (A,A) => Boolean) : (A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A) => Boolean) : (A,A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A,A) => Boolean) : (A,A,A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A,A,A) => Boolean) : (A,A,A,A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A,A,A,A) => Boolean) : (A,A,A,A,A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A,A,A,A,A) => Boolean) : (A,A,A,A,A,A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A,A,A,A,A,A) => Boolean) : (A,A,A,A,A,A,A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A,A,A,A,A,A,A) => Boolean) : (A,A,A,A,A,A,A,A,A) = chooseNotRewritten
  def choose[A](predicate: (A,A,A,A,A,A,A,A,A,A) => Boolean) : (A,A,A,A,A,A,A,A,A,A) = chooseNotRewritten

  // These extractors allow us to write pattern matching expressions that look like arithmetic operators.
  private def extractorNotRewritten: Nothing = error("Illegal use of an arithmetic extractor (use it at top-level only, without guards, and make sure you run scalac with the synthesis plugin).")
  object + {
    def unapply(i: Int): Option[(Int,Int)] = extractorNotRewritten
  }

  object * {
    def unapply(i: Int): Option[(Int,Int)] = extractorNotRewritten
  }

  object - {
    def unapply(i: Int): Option[(Int,Int)] = extractorNotRewritten
  }

  // Function that builds a set by taking a subset of an existing one.
  import scala.collection.immutable.Set
  def take[A](n: Int, from: Set[A]): Set[A] = {
    if (from.size < n) {
      throw new java.lang.IllegalArgumentException("set is too small")
    } else {
      var c: Int = 0
      Set.empty[A] ++ from.takeWhile(x => { c = c + 1; c <= n })
    }
  }
}
