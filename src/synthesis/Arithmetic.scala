package synthesis

import scala.collection.immutable.Set

/** These are the formulas that we extract, and the ones that we plug back in. */
object Arithmetic {
  type VariableID = String

  sealed abstract class Formula {
    override def toString = pp(this)
  }

  class And(val formulas: List[Formula]) extends Formula
  class Or(val formulas: List[Formula]) extends Formula
  case class Not(formula: Formula) extends Formula
  case class True() extends Formula
  case class False() extends Formula
  
  sealed abstract class Predicate extends Formula
  case class Equals(left: Term, right: Term) extends Predicate
  case class NotEquals(left: Term, right: Term) extends Predicate
  case class LessThan(left: Term, right: Term) extends Predicate
  case class LessEqThan(left: Term, right: Term) extends Predicate
  case class GreaterThan(left: Term, right: Term) extends Predicate
  case class GreaterEqThan(left: Term, right: Term) extends Predicate

  sealed abstract class Term {
    override def toString = pp(this)
  }
  case class Variable(id: VariableID) extends Term
  case class IntLit(value: Int) extends Term
  case class Neg(term: Term) extends Term
  class Plus(val terms: List[Term]) extends Term
  case class Minus(left: Term, right: Term) extends Term
  class Times(val terms: List[Term]) extends Term
  case class Div(left: Term, right: Term) extends Term
  case class Modulo(left: Term, right: Term) extends Term
  case class Min(terms: List[Term]) extends Term

  object And {
    def apply(fs: List[Formula]): And = new And(fs)
    def apply(left: Formula, right: Formula): And = (left,right) match {
      case (And(fs1),And(fs2)) => And(fs1 ::: fs2)
      case (And(fs), _) => And(fs ::: List(right))
      case (_, And(fs)) => And(left :: fs)
      case (_, _) => And(List(left,right))
    }
    def unapply(and: And): Option[List[Formula]] = 
      Some(and.formulas)
  }
  object Or {
    def apply(fs: List[Formula]): Or = new Or(fs)
    def apply(left: Formula, right: Formula): Or = (left,right) match {
      case (Or(fs1),Or(fs2)) => Or(fs1 ::: fs2)
      case (Or(fs), _) => Or(fs ::: List(right))
      case (_, Or(fs)) => Or(left :: fs)
      case (_, _) => Or(List(left,right))
    }
    def unapply(or: Or): Option[List[Formula]] = 
      Some(or.formulas)
  }
  object Plus {
    def apply(ts: List[Term]): Plus = new Plus(ts)
    def apply(left: Term, right: Term): Plus = (left,right) match {
      case (Plus(ts1),Plus(ts2)) => Plus(ts1 ::: ts2)
      case (Plus(ts), _) => Plus(ts ::: List(right))
      case (_, Plus(ts)) => Plus(left :: ts)
      case (_, _) => Plus(List(left,right))
    }
    def unapply(plus: Plus): Option[List[Term]] = 
      Some(plus.terms)
  }
  object Times {
    def apply(ts: List[Term]): Times = new Times(ts)
    def apply(left: Term, right: Term): Times = (left,right) match {
      case (Times(ts1),Times(ts2)) => Times(ts1 ::: ts2)
      case (Times(ts), _) => Times(ts ::: List(right))
      case (_, Times(ts)) => Times(left :: ts)
      case (_, _) => Times(List(left,right))
    }
    def unapply(times: Times): Option[List[Term]] = 
      Some(times.terms)
  }

  def variablesOf(f: Formula): Set[VariableID] = f match {
    case And(fs) => fs.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
    case Or(fs) => fs.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
    case Not(f) => variablesOf(f)
    case True() => Set.empty
    case False() => Set.empty
    case Equals(l,r) => variablesOf(l) ++ variablesOf(r)
    case NotEquals(l,r) => variablesOf(l) ++ variablesOf(r)
    case LessThan(l,r) => variablesOf(l) ++ variablesOf(r)
    case LessEqThan(l,r) => variablesOf(l) ++ variablesOf(r)
    case GreaterThan(l,r) => variablesOf(l) ++ variablesOf(r)
    case GreaterEqThan(l,r) => variablesOf(l) ++ variablesOf(r)
  }

  def variablesOf(t: Term): Set[VariableID] = t match {
    case IntLit(_) => Set.empty
    case Variable(id) => Set(id)
    case Neg(t) => variablesOf(t)
    case Plus(ts) => ts.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
    case Minus(l,r) => variablesOf(l) ++ variablesOf(r)
    case Times(ts) => ts.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
    case Div(l,r) => variablesOf(l) ++ variablesOf(r)
    case Modulo(l,r) => variablesOf(l) ++ variablesOf(r)
    case Min(ts) => ts.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
  }

  def NNF(formula: Formula): Formula = {
    def nnf(f: Formula, switch: Boolean): Formula = f match {
      case And(fs) => if(switch) Or(fs.map(nnf(_, true))) else And(fs.map(nnf(_, false)))
      case Or(fs)  => if(switch) And(fs.map(nnf(_, true))) else Or(fs.map(nnf(_, false)))
      case tre @ True()  => if(switch) False() else tre
      case fls @ False() => if(switch) True() else fls
      case Not(f) => nnf(f, !switch)
      case Equals(l,r) if switch => normalizePredicate(NotEquals(l,r))
      case NotEquals(l,r) if switch => normalizePredicate(Equals(l,r))
      case LessThan(l,r) if switch => normalizePredicate(GreaterEqThan(l,r))
      case GreaterEqThan(l,r) if switch => normalizePredicate(LessThan(l,r))
      case GreaterThan(l,r) if switch => normalizePredicate(LessEqThan(l,r))
      case LessEqThan(l,r) if switch => normalizePredicate(GreaterThan(l,r))
      case pred: Predicate => normalizePredicate(pred)
    }
    nnf(formula, false)
  }

  def normalizePredicate(predicate: Predicate): Predicate = predicate match {
    case Equals(l, r) => Equals(linearize(Minus(l, r)), IntLit(0))
    case NotEquals(l, r) => NotEquals(linearize(Minus(l, r)), IntLit(0))
    case LessThan(l, r) => LessThan(linearize(Minus(l, r)), IntLit(0))
    case LessEqThan(l, r) => LessEqThan(linearize(Minus(l, r)), IntLit(0))
    case GreaterThan(l, r) => LessThan(linearize(Minus(r, l)), IntLit(0))
    case GreaterEqThan(l, r) => LessEqThan(linearize(Minus(r, l)), IntLit(0))
  }

  def linearize(term: Term): Term = {
    def noNegs(t: Term): Term = t match {
      case Neg(Neg(t)) => noNegs(t)
      case Neg(IntLit(v)) => IntLit(-v)
      case Neg(Variable(_)) => t
      case Neg(Plus(ts)) => Plus(ts.map((tm: Term) => noNegs(Neg(tm))))
      case Neg(Times(ts)) => noNegs(Times(Neg(ts.head) :: ts.tail))
      case Neg(Minus(l,r)) => noNegs(Minus(r,l))
      case Neg(Div(l,r)) => noNegs(Div(Neg(l), r))
      case Neg(Modulo(l,r)) => noNegs(Modulo(Neg(l), r))
      case Neg(m@Min(ts)) => Neg(noNegs(m))
      case Minus(l,r) => Plus(noNegs(l), noNegs(Neg(r)))
      case Plus(ts) => Plus(ts.map(noNegs(_)))
      case Times(ts) => Plus(ts.map(noNegs(_)))
      case Div(l,r) => Div(noNegs(l), noNegs(r))
      case Modulo(l,r) => Modulo(noNegs(l), noNegs(r))
      case Min(ts) => Min(ts.map(noNegs(_)))
      case IntLit(_) | Variable(_) => t
    }

    noNegs(term)
  }

  /** The rest is only for pretty-printing... */
  private val ANDSTR = " \u2227 "
  private val ORSTR  = " \u2228 "
  private val NOTSTR = "\u00AC"
  private val EQSTR  = " = "
  private val NESTR  = " \u2260 "
  private val LTSTR  = " < "
  private val LESTR  = " \u2264 "
  private val GTSTR  = " > "
  private val GESTR  = " \u2265 "
  private val TRUESTR  = "\u22A4"
  private val FALSESTR = "\u22A5"

  private def pp(f: Formula): String = f match {
    case And(fs) => fs.map(pp(_)).mkString("(", ANDSTR, ")")
    case Or(fs)  => fs.map(pp(_)).mkString("(", ORSTR, ")")
    case Not(f)  => NOTSTR + pp(f)
    case True()  => TRUESTR
    case False() => FALSESTR
    case Equals(l,r) => "(" + pp(l) + EQSTR + pp(r) + ")" 
    case NotEquals(l,r) => "(" + pp(l) + NESTR + pp(r) + ")" 
    case LessThan(l,r) => "(" + pp(l) + LTSTR + pp(r) + ")" 
    case LessEqThan(l,r) => "(" + pp(l) + LESTR + pp(r) + ")" 
    case GreaterThan(l,r) => "(" + pp(l) + GTSTR + pp(r) + ")" 
    case GreaterEqThan(l,r) => "(" + pp(l) + GESTR + pp(r) + ")" 
  }

  private def pp(t: Term): String = t match {
    case Variable(id) => id.toString
    case IntLit(v) => v.toString
    case Neg(t) => "~" + pp(t)
    case Plus(ts) => ts.map(pp(_)).mkString("(", " + ", ")")
    case Minus(l,r) => "(" + pp(l) + " - " + pp(r) + ")"
    case Times(ts) => ts.map(pp(_)).mkString("(", " * ", ")")
    case Div(l,r) => "(" + pp(l) + " / " + pp(r) + ")"
    case Modulo(l,r) => "(" + pp(l) + " % " + pp(r) + ")"
    case Min(ts) => "min " + ts.map(pp(_)).mkString("{", ", ", "}")
  }
}
