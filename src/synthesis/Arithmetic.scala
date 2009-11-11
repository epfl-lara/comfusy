package synthesis

import scala.collection.immutable.Set

/** These are the formulas that we extract, and the ones that we plug back in. */
object Arithmetic {
  type VariableID = String

  abstract class Formula {
    override def toString = pp(this)
  }

  case class And(formulas: List[Formula]) extends Formula
  case class Or(formulas: List[Formula]) extends Formula
  case class Not(formula: Formula) extends Formula
  case class True() extends Formula
  case class False() extends Formula
  
  abstract class Predicate extends Formula
  case class Equals(left: Term, right: Term) extends Predicate
  case class NotEquals(left: Term, right: Term) extends Predicate
  case class LessThan(left: Term, right: Term) extends Predicate
  case class LessEqThan(left: Term, right: Term) extends Predicate
  case class GreaterThan(left: Term, right: Term) extends Predicate
  case class GreaterEqThan(left: Term, right: Term) extends Predicate

  abstract class Term {
    override def toString = pp(this)
  }
  case class Variable(id: VariableID) extends Term
  case class IntLit(value: Int) extends Term
  case class Neg(term: Term) extends Term
  case class Plus(left: Term, right: Term) extends Term
  case class Minus(left: Term, right: Term) extends Term
  case class Times(left: Term, right: Term) extends Term
  case class Div(left: Term, right: Term) extends Term
  case class Modulo(left: Term, right: Term) extends Term
  case class Min(terms: List[Term]) extends Term

  /** An extractor to pattern-match on predicates. */
  object Predicate {
    def unapply(pred: Predicate): Option[(Term,Term)] = pred match {
      case Equals(l,r) => Some((l,r))
      case NotEquals(l,r) => Some((l,r))
      case LessThan(l,r) => Some((l,r))
      case LessEqThan(l,r) => Some((l,r))
      case GreaterThan(l,r) => Some((l,r))
      case GreaterEqThan(l,r) => Some((l,r))
    }
  }

  object BinaryOperator {
    def unapply(term: Term): Option[(Term,Term)] = term match {
      case Plus(l,r) => Some((l,r))
      case Minus(l,r) => Some((l,r))
      case Times(l,r) => Some((l,r))
      case Div(l,r) => Some((l,r))
      case Modulo(l,r) => Some((l,r))
      case _ => None
    }
  }

  def variablesOf(f: Formula): Set[VariableID] = f match {
    case And(fs) => fs.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
    case Or(fs) => fs.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
    case Not(f) => variablesOf(f)
    case True() => Set.empty
    case False() => Set.empty
    case Predicate(l,r) => variablesOf(l) ++ variablesOf(r)
  }

  def variablesOf(t: Term): Set[VariableID] = t match {
    case Variable(id) => Set(id)
    case Neg(t) => variablesOf(t)
    case BinaryOperator(l,r) => variablesOf(l) ++ variablesOf(r)
    case Min(ts) => ts.foldLeft(Set.empty[VariableID])(_ ++ variablesOf(_))
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
    case Neg(t) => "-" + pp(t)
    case Plus(l,r) => "(" + pp(l) + " + " + pp(r) + ")"
    case Minus(l,r) => "(" + pp(l) + " - " + pp(r) + ")"
    case Times(l,r) => "(" + pp(l) + " * " + pp(r) + ")"
    case Div(l,r) => "(" + pp(l) + " / " + pp(r) + ")"
    case Modulo(l,r) => "(" + pp(l) + " % " + pp(r) + ")"
    case Min(ts) => "min " + ts.map(pp(_)).mkString("{", ", ", "}")
  }
}
