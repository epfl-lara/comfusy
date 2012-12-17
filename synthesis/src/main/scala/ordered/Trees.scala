package synthesis.ordered

object Trees { /* dummy */ }

object OrderedTrees {
  sealed abstract class Formula {
    override def toString = pp(this)
  }
  case class And(f1: Formula, f2: Formula) extends Formula
  case class Or(f1: Formula, f2: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class FAtom(a: Atom) extends Formula

  sealed abstract class Atom {
    override def toString = pp(this)
  }
  case class TermEqual(i1: PAInt, i2: PAInt) extends Atom
  case class TermLessEqual(i1: PAInt, i2: PAInt) extends Atom
  case class TermIsInt(i1: PAInt) extends Atom // TODO PAInt -> Real
  case class SetEqual(s1: BASet, s2: BASet) extends Atom
  case class SetLess(s1: BASet, s2: BASet) extends Atom
  case class SetElem(t1: PAInt, s2: BASet) extends Atom // TODO PAInt -> Real
  //  case class SetIsOnlyIntegers(s1: BASet) extends Atom
  case class SetIsInfinite(s1: BASet) extends Atom
  case class SetCard(s1: BASet, t1: PAInt) extends Atom
  case class SetInf(s1: BASet, t1: PAInt) extends Atom // TODO PAInt -> Real
  case class SetSup(s1: BASet, t1: PAInt) extends Atom // TODO PAInt -> Real
  //  case class SetHasNoInf(s1: BASet) extends Formula
  //  case class SetHasNoSup(s1: BASet) extends Formula

  sealed abstract class PAInt {
    override def toString = pp(this)
  }
  case class TermVar(i: String) extends PAInt
  case class IntConst(c: Int) extends PAInt
  case class Plus(i1: PAInt, i2: PAInt) extends PAInt
  case class Times(c: Int, i2: PAInt) extends PAInt
  //  case class Card(s: BASet) extends PAInt

  sealed abstract class BASet {
    override def toString = pp(this)
  }
  case class SetVar(name: String) extends BASet
  case object EmptySet extends BASet
  case object UnivSet extends BASet
  case class Union(s1: BASet, s2: BASet) extends BASet
  case class Intersec(s1: BASet, s2: BASet) extends BASet
  case class Compl(s: BASet) extends BASet
  case class Take(n1: PAInt, s1: BASet) extends BASet


  object LRange {
    def apply(t1: PAInt, t2: PAInt, s1: SetVar) = {
      Intersec(Take(t2, s1), Compl(Take(Plus(t1, IntConst(-1)), s1)))
    }
  }

  // S1 c= S2  is expressed as S1 = S1 n S2
  object SetSubset {
    def apply(s1: SetVar, s2: BASet) = {
      SetEqual(s1, Intersec(s1, s2))
    }
  }

  object TermLess {
    //    def apply(t1: TermVar, t2: TermVar) = {
    def apply(t1: PAInt, t2: PAInt) = {
      And(TermLessEqual(t1, t2), Not(TermEqual(t1, t2)))
    }
  }

  object Minus {
    def apply(t1: PAInt, t2: PAInt) = {
      Plus(t1, Times(-1, t2))
    }
  }

  val True: Formula = TermEqual(IntConst(0), IntConst(0))

  implicit def atom2formula(a: Atom): Formula = FAtom(a)

  def makeAnd(fs: List[Formula]): Formula = fs match {
    case Nil => True
    case f :: Nil => f
    case f :: fs => (f /: fs)(And(_, _))
  }

  def makeAnd(f0: Formula, fs: Formula*): Formula =
    makeAnd(f0 :: fs.toList)

  def makeUnion(ss: List[BASet]): BASet = ss match {
    case Nil => EmptySet
    case s :: Nil => s
    case s :: ss => (s /: ss)(Union(_, _))
  }


  /**The rest is only for pretty-printing... */

  private val ANDSTR = " \u2227 "
  private val ORSTR = " \u2228 "
  private val NOTSTR = "\u00AC"
  private val EQSTR = " = "
  private val NESTR = " \u2260 "
  private val LTSTR = " < "
  private val LESTR = " \u2264 "
  private val GTSTR = " > "
  private val GESTR = " \u2265 "
  private val TRUESTR = "\u22A4"
  private val FALSESTR = "\u22A5"

  val UNIONSTR = " \u222A "
  val INTERSTR = " \u2229 "
  val SUBSETEQSTR = " \u2286 "
  val SETLESSSTR = " \u227A "
  val SETELEMSTR = " \u2208 "
  val INFSTR = " \u221E "
  val ZSTR = " \u2124 "

  private def pp(f: Formula): String = f match {
    case And(l, r) => "(" + pp(l) + ANDSTR + pp(r) + ")"
    case Or(l, r) => "(" + pp(l) + ORSTR + pp(r) + ")"
    case Not(FAtom(a)) => NOTSTR + "(" + pp(a) + ")"
    case Not(f) => NOTSTR + pp(f)
    case FAtom(a) => pp(a)
  }

  private def pp(t: PAInt): String = t match {
    case TermVar(id) => id.toString
    case IntConst(v) => v.toString
    case Plus(l, r) => "(" + pp(l) + " + " + pp(r) + ")"
    case Times(c, t) => "(" + c + " * " + pp(t) + ")"
  }

  private def pp(s: BASet): String = s match {
    case SetVar(id) => id.toString
    case EmptySet => "<empty>"
    case UnivSet => "<universal>"
    case Union(l, r) => "(" + pp(l) + UNIONSTR + pp(r) + ")"
    case Intersec(l, r) => "(" + pp(l) + INTERSTR + pp(r) + ")"
    case Compl(s) => pp(s) + "^c"
    case Take(n, s) => "Take( + " + pp(n) + ", " + pp(s) + ")"
  }

  private def pp(a: Atom): String = a match {
    case TermEqual(l, r) => pp(l) + EQSTR + pp(r)
    case TermLessEqual(l, r) => pp(l) + LESTR + pp(r)
    case TermIsInt(t) => pp(t) + EQSTR + ZSTR
    case SetEqual(l, r) => pp(l) + EQSTR + pp(r)
    case SetLess(l, r) => pp(l) + SETLESSSTR + pp(r)
    case SetElem(l, r) => pp(l) + SETELEMSTR + pp(r)
    //    case SetIsOnlyIntegers(s) => pp(s) + SUBSETEQSTR + ZSTR
    case SetIsInfinite(s) => "|" + pp(s) + "|" + GESTR + INFSTR
    case SetCard(l, r) => "|" + pp(l) + "|" + EQSTR + pp(r)
    case SetInf(l, r) => "sup(" + pp(l) + ")" + EQSTR + pp(r)
    case SetSup(l, r) => "inf(" + pp(l) + ")" + EQSTR + pp(r)
  }

}
