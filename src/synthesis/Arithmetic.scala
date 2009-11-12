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
    def apply(ts: List[Term]): Term = ts.length match {
      case 0 => IntLit(0)
      case 1 => ts.head
      case _ => new Plus(ts.flatMap(t => if (t.isInstanceOf[Plus]) t.asInstanceOf[Plus].terms else List(t)))
    }
    def apply(left: Term, right: Term): Term = (left,right) match {
      case (Plus(ts1),Plus(ts2)) => Plus(ts1 ::: ts2)
      case (Plus(ts), _) => Plus(ts ::: List(right))
      case (_, Plus(ts)) => Plus(left :: ts)
      case (_, _) => Plus(List(left,right))
    }
    def unapply(plus: Plus): Option[List[Term]] = 
      Some(plus.terms)
  }
  object Times {
    def apply(ts: List[Term]): Term = ts.length match {
      case 0 => IntLit(1)
      case 1 => ts.head
      case _ => new Times(ts.flatMap(t => if (t.isInstanceOf[Times]) t.asInstanceOf[Times].terms else List(t)))
    }
    def apply(left: Term, right: Term): Term = (left,right) match {
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

  def normalized(formula: Formula): Formula = {
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

    // rewrites all predicates into ... = 0 and ... >= 0
    def normalizePredicate(predicate: Predicate): Formula = predicate match {
      case Equals(l, r) => Equals(linearize(Minus(l, r)), IntLit(0))
      case NotEquals(l, r) => { Or(
          normalizePredicate(LessThan(l,r)),
          normalizePredicate(LessThan(r,l))
        )}
      case LessThan(l, r) => normalizePredicate(GreaterThan(Minus(r,l), IntLit(0)))
      case LessEqThan(l, r) => GreaterEqThan(linearize(Minus(r,l)), IntLit(0))
      case GreaterThan(l, r) => GreaterEqThan(linearize(Plus(Minus(l,r), IntLit(-1))), IntLit(0))
      case GreaterEqThan(l, r) => GreaterEqThan(linearize(Minus(l,r)), IntLit(0))
    }
  
    def linearize(term: Term): Term = {
      // removes all minus and neg terms by pushing them into the constants.
      def noNegs(t: Term): Term = t match {
        case Neg(Neg(t)) => noNegs(t)
        case Neg(IntLit(v)) => IntLit(-v)
        case Neg(v: Variable) => Times(IntLit(-1), v) 
        case Neg(Plus(ts)) => Plus(ts.map((tm: Term) => noNegs(Neg(tm))))
        case Neg(Times(ts)) => noNegs(Times(Neg(ts.head) :: ts.tail))
        case Neg(Minus(l,r)) => noNegs(Minus(r,l))
        case Neg(Div(l,r)) => noNegs(Div(Neg(l), r))
        case Neg(Modulo(l,r)) => noNegs(Modulo(Neg(l), r))
        case Neg(m@Min(ts)) => Neg(noNegs(m))
        case Minus(l,r) => Plus(noNegs(l), noNegs(Neg(r)))
        case Plus(ts) => Plus(ts.map(noNegs(_)))
        case Times(ts) => Times(ts.map(noNegs(_)))
        case Div(l,r) => Div(noNegs(l), noNegs(r))
        case Modulo(l,r) => Modulo(noNegs(l), noNegs(r))
        case Min(ts) => Min(ts.map(noNegs(_)))
        case IntLit(_) | Variable(_) => t
      }
  
      // distributes multiplications over sums. assumes that everything is
      // already products or sums (ie. noNegs was applied and there are no mins,
        // divs and mods)
      def dist(term: Term): Term = term match {
        case Times(t1 :: t1s) => t1 match {
          case Plus(t2 :: t2s) => Plus(dist(Times(t2 :: List(Times(t1s)))) :: List(dist(Times(Plus(t2s) :: t1s))))
          case otherTerm => {
            dist(Times(t1s)) match {
              case Plus(tps) => Plus(tps.map(t => Times(otherTerm :: t :: Nil)))
              case other => Times(otherTerm :: other :: Nil)
            }
          }
        }
        case Plus(ts) => Plus(ts.map(dist(_)))
        case _ => term
      }
  
      // tries to simplify a term (not recursively)
      def simpler(term: Term): Term = term match {
        case Plus(ts0) => {
          val ts = ts0.map(simpler(_))
            val cstSum = ts.map(t => t match {
              case IntLit(v) => v
              case _ => 0
            }).foldLeft(0)(_ + _)
          val noCst = ts.filter(t => !t.isInstanceOf[IntLit])
            if(cstSum != 0)
            Plus(IntLit(cstSum) :: noCst)
          else
            Plus(noCst)        
        }
  
        case Times(ts0) => {
          val ts = ts0.map(simpler(_))
            val cstProd = ts.map(t => t match {
              case IntLit(v) => v
              case _ => 1
            }).foldLeft(1)(_ * _)
          val noCst = ts.filter(t => !t.isInstanceOf[IntLit])
            if(cstProd == 0)
            IntLit(0)
          else if(cstProd != 1)
            Times(IntLit(cstProd) :: noCst)
          else
            Times(noCst)        
        }
  
        case _ => term
      }
  
      simpler(dist(noNegs(term)))
    }

    nnf(formula, false)
  }


  object LinearCombination {
    private object CoefProduct {
      def unapply(term: Term) : Option[(String,Int)] = term match {
        case IntLit(v) => Some(("", v))
        case Variable(nme) => Some((nme,1))
        case Times(IntLit(c) :: Variable(nme) :: Nil) => Some((nme,c))
        case Times(Variable(nme) :: IntLit(c) :: Nil) => Some((nme,c))
        case _ => None
      }
    }

    def unapply(term: Term) : Option[(Int,List[(String,Int)])] = term match {
      case IntLit(v) => Some((v,Nil))
      case CoefProduct(nme,c) => Some((0,List((nme,c))))
      case Plus(ts) => {
        val cps: List[Option[(String,Int)]] = ts.map(t => CoefProduct.unapply(t))
        if (cps.exists(_.isEmpty)) // the sum was not over linear terms !
          None
        else {
          val sums = new scala.collection.mutable.HashMap[String,Int]
          for((varnme, coef) <- cps.map(_.get)) {
            sums(varnme) = sums.getOrElse(varnme,0) + coef
          }
          val cstcoef = sums.getOrElse("",0)
          sums.removeKey("")
          Some(cstcoef,sums.toList)
        }
      }
      case _ => None
    }
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
