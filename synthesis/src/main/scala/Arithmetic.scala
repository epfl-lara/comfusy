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
    def apply(fs: List[Formula]): Formula = fs match {
      case Nil => True()
      case f :: Nil => f
      case fs if fs.contains(False()) => False()
      case fs if fs.contains(True()) => And(fs.filter(_ != True()))
      case _ => new And(fs)
    }
    def apply(left: Formula, right: Formula): Formula = (left,right) match {
      case (And(fs1),And(fs2)) => And(fs1 ::: fs2)
      case (And(fs), _) => And(fs ::: List(right))
      case (_, And(fs)) => And(left :: fs)
      case (_, _) => And(List(left,right))
    }
    def unapply(and: And): Option[List[Formula]] =
      Some(and.formulas)
  }
  object Or {
    def apply(fs: List[Formula]): Formula = fs match {
      case Nil => False()
      case f :: Nil => f
      case fs if fs.contains(True()) => True()
      case fs if fs.contains(False()) => Or(fs.filter(_ != False()))
      case _ => new Or(fs)
    }
    def apply(left: Formula, right: Formula): Formula = (left,right) match {
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
      case (IntLit(0), t) => t
      case (t, IntLit(0)) => t
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
      case (IntLit(0), _) => IntLit(0)
      case (_, IntLit(0)) => IntLit(0)
      case (IntLit(1), t) => t
      case (t, IntLit(1)) => t
      case (IntLit(-1), t) => Neg(t)
      case (t, IntLit(-1)) => Neg(t)
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

  def renameVarSet(form: Formula, varSet: Set[String]): (Formula,Map[String,String],Map[String,String]) = {
    import scala.collection.mutable.HashMap
    val varsInForm = variablesOf(form)
    val prefixUses = new HashMap[String,Int]
    var toMap      = Map.empty[String,String]
    var fromMap    = Map.empty[String,String]
    def freshName(prefix: String): String = {
      var next = (prefixUses.getOrElse(prefix, -1) + 1)
      while(varsInForm.contains(prefix + next)) {
        next = next + 1
      }
      prefixUses(prefix) = next
      prefix + next
    }

    def travF(frm: Formula): Formula = frm match {
      case And(fs) => And(fs.map(travF(_)))
      case Or(fs) => Or(fs.map(travF(_)))
      case Not(f) => Not(travF(f))
      case True() | False() => frm
      case Equals(l,r) => Equals(travT(l), travT(r))
      case NotEquals(l,r) => NotEquals(travT(l), travT(r))
      case LessThan(l,r) => LessThan(travT(l), travT(r))
      case LessEqThan(l,r) => LessEqThan(travT(l), travT(r))
      case GreaterThan(l,r) => GreaterThan(travT(l), travT(r))
      case GreaterEqThan(l,r) => GreaterEqThan(travT(l), travT(r))
    }

    def travT(trm: Term): Term = trm match {
      case IntLit(_) => trm
      case Variable(id) if varSet.contains(id) => {
        if(toMap.isDefinedAt(id))
          Variable(toMap(id))
        else {
          val nn = freshName(id)
          toMap = toMap + (id -> nn)
          fromMap = fromMap + (nn -> id)
          Variable(nn)
        }
      }
      case Variable(_) => trm
      case Neg(t) => Neg(travT(t))
      case Plus(ts) => Plus(ts.map(travT(_)))
      case Minus(l,r) => Minus(travT(l), travT(r))
      case Times(ts) => Times(ts.map(travT(_)))
      case Div(l,r) => Div(travT(l), travT(r))
      case Modulo(l,r) => Modulo(travT(l), travT(r))
      case Min(ts) => Min(ts.map(travT(_)))
    }

    // actually, we force this first, or if the variables don't appear we'll be
    // in trouble.
    for(v <- varSet) {
      val vf = freshName(v)
      toMap = toMap + (v -> vf)
      fromMap = fromMap + (vf -> v)
    }

    val nf = travF(form)
    (nf,toMap,fromMap)
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
      case Equals(l, r) => {
        val lnrz = linearize(Minus(l, r))
        if (lnrz == IntLit(0))
          True()
        else
          Equals(lnrz, IntLit(0))
      }
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

  // checks that there is never a multiplicative term with a restricted var on
  // both sides
  def isQuasiLinear(form: Formula, restricted: Set[VariableID]) : Boolean = {
    def iql(f: Formula) : Boolean = f match {
      case And(fs) => fs.forall(iql(_))
      case Or(fs) => fs.forall(iql(_))
      case Not(fm) => iql(fm)
      case True() | False() => true
      case Equals(l,r) => iqlt(l) && iqlt(r)
      case NotEquals(l,r) => iqlt(l) && iqlt(r)
      case LessThan(l,r) => iqlt(l) && iqlt(r)
      case LessEqThan(l,r) => iqlt(l) && iqlt(r)
      case GreaterThan(l,r) => iqlt(l) && iqlt(r)
      case GreaterEqThan(l,r) => iqlt(l) && iqlt(r)
    }

    def iqlt(t: Term) : Boolean = t match {
      case Variable(id) => true
      case IntLit(v) => true
      case Neg(t) => true
      case Plus(ts) => ts.forall(iqlt(_))
      case Minus(l,r) => iqlt(l) && iqlt(r)
      case Times(ts) => {
        val varSets: List[Set[VariableID]] = ts.map(variablesOf(_)).map(_ ** restricted)

        var ok = true
        for(val vs1 <- varSets) {
          for(val vs2 <- varSets) {
            if(!(vs1 eq vs2) && !(vs1 ** vs2).isEmpty) {
              ok = false
              //println("CE: " + vs1 + " ... " + vs2)
            }
          }
        }
        ok
      }
      case Div(l,r) => false // not entirely accurate, but goes well with what we extract :)
      case Modulo(l,r) => false // same as above
      case Min(ts) => ts.forall(iqlt(_))
    }

    iql(form)
  }

  object LinearCombination {
    private object CoefProduct {
      def unapply(term: Term) : Option[(String,Int)] = term match {
        case IntLit(v) => Some(("", v))
        case Variable(nme) => Some((nme,1))
        case Neg(Variable(nme)) => Some((nme,-1))
        case Times(IntLit(c) :: Variable(nme) :: Nil) => Some((nme,c))
        case Times(IntLit(c) :: Neg(Variable(nme)) :: Nil) => Some((nme,-c))
        case Times(Variable(nme) :: IntLit(c) :: Nil) => Some((nme,c))
        case Times(Neg(Variable(nme)) :: IntLit(c) :: Nil) => Some((nme,-c))
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
          val cstcoef = sums.getOrElse("", 0)
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

  def toSMTBenchmark(form: Formula): String = {
    // the main problem is that we need to encode things like division, min and
    // modulo. We add "local equalities" for that.
    lazy val varsInForm = variablesOf(form)

    val prefixUses = new scala.collection.mutable.HashMap[String,Int]
    def freshName(prefix: String): String = {
      var next = (prefixUses.getOrElse(prefix, -1) + 1)
      while(varsInForm.contains(prefix + next)) {
        next = next + 1
      }
      prefixUses(prefix) = next
      prefix + next
    }

    val newEqs = new scala.collection.mutable.HashMap[String,Term]
    def addEq(nme: String, term: Term): Unit = {
      newEqs(nme) = term
    }
    val newForms = new scala.collection.mutable.HashSet[Formula]
    def addFormula(f: Formula): Unit = {
      newForms(f) = true
    }

    def flatten(trm: Term): Term = trm match {
      case v: Variable => v
      case i: IntLit => i
      case Neg(t) => Neg(flatten(t))
      case Plus(ts) => Plus(ts.map(flatten(_)))
      case Minus(l,r) => Minus(flatten(l), flatten(r))
      case Times(ts) => Times(ts.map(flatten(_)))
      case Div(l,r) => {
        val lf = flatten(l)
        val rf = flatten(r)
        val res = Variable(freshName("divRes"))
        val rem = Variable(freshName("divRem"))
        addFormula(Equals(Times(res, rf), Minus(lf, rem)))
        addFormula(GreaterEqThan(rem, IntLit(0)))
        addFormula(LessThan(rem, rf))
        addEq(res.id, res)
        addEq(rem.id, rem)
        res
      }
      case Modulo(l,r) => {
        val lf = flatten(l)
        val rf = flatten(r)
        val res = Variable(freshName("modRes"))
        val coe = Variable(freshName("modCoe"))
        addFormula(Equals(lf, Plus(res, Times(rf, coe))))
        addFormula(GreaterEqThan(res, IntLit(0)))
        addFormula(LessThan(res, rf))
        addEq(res.id, res)
        addEq(coe.id, coe)
        res
      }
      case Min(ts) => Min(ts.map(flatten(_)))
    }

    def f2s(frm: Formula): String = frm match {
      case And(fs) => "(and " + fs.map(f2s(_)).mkString(" ") + ')'
      case Or(fs) => "(or " + fs.map(f2s(_)).mkString(" ") + ')'
      case Not(f) => "(not " + f2s(f) + ')'
      case True() => "true"
      case False() => "false"
      case Equals(l,r) => "(= " + t2s(flatten(l)) + ' ' + t2s(flatten(r)) + ')'
      case NotEquals(l,r) => "(distinct " + t2s(flatten(l)) + ' ' + t2s(flatten(r)) + ')'
      case LessThan(l,r) => "(< " + t2s(flatten(l)) + ' ' + t2s(flatten(r)) + ')'
      case LessEqThan(l,r) =>"(<= " + t2s(flatten(l)) + ' ' + t2s(flatten(r)) + ')'
      case GreaterThan(l,r) =>"(> " + t2s(flatten(l)) + ' ' + t2s(flatten(r)) + ')'
      case GreaterEqThan(l,r) =>"(>= " + t2s(flatten(l)) + ' ' + t2s(flatten(r)) + ')'
    }

    def t2s(trm: Term): String = trm match {
      case Variable(id) => id.toString
      case IntLit(v) => if(v < 0) "(~ " + (-v).toString + ')' else v.toString
      case Neg(t) => "(~ " + t2s(t) + ')'
      case Plus(ts) => ts.map(t2s(_)).reduceLeft((s1:String,s2:String) => "(+ " + s1 + ' ' + s2 + ')')
      case Minus(l,r) => "(- " + t2s(l) + ' ' + t2s(r) + ')'
      case Times(ts) => ts.map(t2s(_)).reduceLeft((s1:String,s2:String) => "(* " + s1 + ' ' + s2 + ')')
      case Div(l,r) => "(/ " + t2s(l) + ' ' + t2s(r) + ')'
      case Modulo(l,r) => "(% " + t2s(l) + " " + t2s(r) + ")"
      case Min(ts) => {
        ts.map(t => {
          val fresh = freshName("inMin")
          addEq(fresh, t)
          t2s(Variable(fresh))
        }).reduceLeft((s1:String,s2:String) => "(ite (< " + s1 + " " + s2 + ") " + s1 + " " + s2 + ")")
      }
    }

    var str = "(benchmark X\n :logic QF_LIA \n :status unknown\n"

    // because of side effects, you need to do this now, or you won't know
    // which variables have been added !
    val formulaString = f2s(form)

    if(!(varsInForm.isEmpty && newEqs.isEmpty)) {
      str = str + " :extrafuns ( "
      varsInForm.foreach(vn => {
        str = str + "(" + vn.toString + " Int) "
      })
      newEqs.keys.foreach(vn => {
        str = str + "(" + vn.toString + " Int) "
      })
      str = str + ")\n"
    }

    for((nme,trm) <- newEqs) {
      str = str + " :assumption (= " + nme + " " + t2s(trm) + ")\n"
    }

    for(frm <- newForms) {
      // note that this breaks if one of the new formulas has not been
      // flattened...
      str = str + " :assumption " + f2s(frm) + "\n"
    }

    str = str + " :formula \n"
    str = str + formulaString
    str = str + "\n)"
    str
  }

  // uses Z3 to check for satisfiability, and gives a model if SAT
  def isSat(form: Formula): (Option[Boolean],Option[Map[String,Int]]) = {
    try {
      val varsInForm = variablesOf(form)
      val process = java.lang.Runtime.getRuntime.exec("z3 -smt -in")
      val out     = new java.io.PrintStream(process.getOutputStream)
      val smt = toSMTBenchmark(form)
      out.println(smt)
      // println(smt)
      out.flush
      out.close
      val in = new java.io.BufferedReader(new java.io.InputStreamReader(process.getInputStream))
      var line: String = in.readLine
      var lines: List[String] = Nil
      while(line != null) {
        lines = line :: lines
        line = in.readLine
      }
      lines = lines.reverse

      var ass = Map.empty[String,Int]
      var status: Option[Boolean] = None

      for (val l <- lines) {
        if(l.contains(" -> ")) {
          val spl = l.split(" -> ")
          if(varsInForm.contains(spl(0)))
            ass = ass + (spl(0) -> spl(1).toInt)
        } else if(l.contains("unsat")) {
          status = Some(false)
        } else if(l == "sat") {
          status = Some(true)
        }
      }
      (status, if(status == Some(true)) Some(ass) else None)
    } catch {
      case (e: java.io.IOException) => {
        Console.err.println("Warning: Cannot execute Z3. Is the executable in the path?.\n")
        (None,None)
      }
    }
  }
}
