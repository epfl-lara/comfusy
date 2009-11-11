package synthesis

import scala.collection.immutable.Set

/** These are the formulas that we extract, and the ones that we plug back in. */
object Arithmetic {
  type VariableID = String

  abstract class Formula

  case class And(formulas: List[Formula]) extends Formula
  case class Or(formulas: List[Formula]) extends Formula
  case class Not(formula: Formula) extends Formula
  case class True() extends Formula
  case class False() extends Formula
  
  abstract class Predicate extends Formula
  case class Equals(left: Term, right: Term) extends Predicate
  case class LessThan(left: Term, right: Term) extends Predicate
  case class LessEqThan(left: Term, right: Term) extends Predicate
  case class GreaterThan(left: Term, right: Term) extends Predicate
  case class GreaterEqThan(left: Term, right: Term) extends Predicate

  abstract class Term
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
}
