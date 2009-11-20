package synthesis.bapa

  sealed abstract class PAInt
  case class IntVar(val i: String) extends PAInt
  case class IntConst(val c: Int) extends PAInt
  case class Plus(val i1: PAInt, val i2: PAInt) extends PAInt
  case class Times(val c: Int, val i2: PAInt) extends PAInt
  case class Card(val s: BASet) extends PAInt

  sealed abstract class BASet
  case class SetVar(val s:String) extends BASet
  case object EmptySet extends BASet
  case object UnivSet extends BASet
  case class Union(val s1: BASet, val s2: BASet) extends BASet
  case class Intersec(val s1: BASet, val s2: BASet) extends BASet
  case class Compl(val s: BASet) extends BASet

  sealed abstract class Atom
  case class SetEqual(val s1: BASet, val s2: BASet) extends Atom
  case class SetSubset(val s1: BASet, val s2: BASet) extends Atom
  case class IntEqual(val i1: PAInt, val i2: PAInt) extends Atom
  case class IntLessEqual(val i1: PAInt, val i2: PAInt) extends Atom
  case class IntDivides(val c:Int, val i: PAInt) extends Atom

  sealed abstract class Formula
  case class And(val f1: Formula, val f2: Formula) extends Formula
  case class Or(val f1: Formula, val f2: Formula) extends Formula
  case class Not(val f: Formula) extends Formula
  case class FAtom(val a: Atom) extends Formula

  // \forall x \forall k \exists y \exists l. F(x, y, k, l), x, y sets, k, l integers
  case class Task(val x: List[String], val y: List[String], val k: List[String], val l: List[String], val f: Formula)

  sealed abstract class SetAssignment
  case class Take(setName: String, firstCount: PAInt, fromSet: BASet) extends SetAssignment
  case class Simple(setName: String, fromSet: BASet) extends SetAssignment


