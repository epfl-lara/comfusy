package synthesis.bapa

object ASTBAPASyn {
  sealed abstract class PAInt
  case class IntVar(i: String) extends PAInt
  case class IntConst(c: Int) extends PAInt
  case class Plus(i1: PAInt, i2: PAInt) extends PAInt
  case class Times(c: Int, i2: PAInt) extends PAInt
  case class Card(s: BASet) extends PAInt

  sealed abstract class BASet
  case class SetVar(s:String) extends BASet
  case object EmptySet extends BASet
  case object UnivSet extends BASet
  case class Union(s1: BASet, s2: BASet) extends BASet
  case class Intersec(s1: BASet, s2: BASet) extends BASet
  case class Compl(s: BASet) extends BASet

  sealed abstract class Atom
  case class SetEqual(s1: BASet, s2: BASet) extends Atom
  case class SetSubset(s1: BASet, s2: BASet) extends Atom
  case class IntEqual(i1: PAInt, i2: PAInt) extends Atom
  case class IntLessEqual(i1: PAInt, i2: PAInt) extends Atom
  case class IntDivides(c:Int, i: PAInt) extends Atom

  sealed abstract class Formula
  case class And(f1: Formula, f2: Formula) extends Formula
  case class Or(f1: Formula, f2: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class FAtom(a: Atom) extends Formula

  // \forall x \forall k \exists y \exists l. F(x, y, k, l), x, y sets, k, l integers
  case class Task(x: List[String], y: List[String], k: List[String], l: List[String], f: Formula)

  sealed abstract class SetAssignment
  case class Take(setName: String, firstCount: PAInt, fromSet: BASet) extends SetAssignment
  case class Simple(setName: String, fromSet: BASet) extends SetAssignment

// =============================



  def bapaFormToArithForm(form: Formula): Arithmetic.Formula = {
    def f2f(f: Formula): Arithmetic.Formula = f match {
      case And(f1, f2) => Arithmetic.And(f2f(f1), f2f(f2))
      case Or(f1, f2) => Arithmetic.Or(f2f(f1), f2f(f2))
      case class Not(f)  => Arithmetic.Not(f2f(f1))
      case class FAtom(a) => bapaAtoArithForm(a)
    }
    f2f(form)
  }

  def bapaAtoArithForm(a: Atom): Arithmetic.Formula = {

  }
     case _ => scala.Predef.error("Not arithmetic formula !!! " + f)



}
