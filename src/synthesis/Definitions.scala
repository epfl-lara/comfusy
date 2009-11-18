package synthesis

/** All definitions which are meant to be used ``as the library''.  */
object Definitions {
  /** This exception is thrown when the constraint-solving generated code can not solve the constraints. */
  case class UnsatisfiableConstraint() extends Exception("The constraints cannot be satisfied.")

  private def chooseNotRewritten: Nothing = error("``choose'' was not rewritten by the synthesis plugin")
  def choose[A1](predicate: A1 => Boolean) : A1 = chooseNotRewritten
  def choose[A1,A2](predicate: (A1,A2) => Boolean) : (A1,A2) = chooseNotRewritten
  def choose[A1,A2,A3](predicate: (A1,A2,A3) => Boolean) : (A1,A2,A3) = chooseNotRewritten
  def choose[A1,A2,A3,A4](predicate: (A1,A2,A3,A4) => Boolean) : (A1,A2,A3,A4) = chooseNotRewritten
  def choose[A1,A2,A3,A4,A5](predicate: (A1,A2,A3,A4,A5) => Boolean) : (A1,A2,A3,A4,A5) = chooseNotRewritten
  def choose[A1,A2,A3,A4,A5,A6](predicate: (A1,A2,A3,A4,A5,A6) => Boolean) : (A1,A2,A3,A4,A5,A6) = chooseNotRewritten
  def choose[A1,A2,A3,A4,A5,A6,A7](predicate: (A1,A2,A3,A4,A5,A6,A7) => Boolean) : (A1,A2,A3,A4,A5,A6,A7) = chooseNotRewritten
  def choose[A1,A2,A3,A4,A5,A6,A7,A8](predicate: (A1,A2,A3,A4,A5,A6,A7,A8) => Boolean) : (A1,A2,A3,A4,A5,A6,A7,A8) = chooseNotRewritten
  def choose[A1,A2,A3,A4,A5,A6,A7,A8,A9](predicate: (A1,A2,A3,A4,A5,A6,A7,A8,A9) => Boolean) : (A1,A2,A3,A4,A5,A6,A7,A8,A9) = chooseNotRewritten
  def choose[A1,A2,A3,A4,A5,A6,A7,A8,A9,A10](predicate: (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10) => Boolean) : (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10) = chooseNotRewritten

  // These extractors allow us to write pattern matching expressions which look like arithmetic operators.
  private def extractorNotRewritten: Nothing = error("an arithmetic extractor was not rewritten by the synthesis plugin")
  object + {
    def unapply(i: Int): Option[(Int,Int)] = extractorNotRewritten
  }

  object * {
    def unapply(i: Int): Option[(Int,Int)] = extractorNotRewritten
  }

  object - {
    def unapply(i: Int): Option[(Int,Int)] = extractorNotRewritten
  }
}
