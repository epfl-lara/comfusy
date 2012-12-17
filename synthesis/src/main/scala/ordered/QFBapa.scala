package synthesis
package ordered

import synthesis.{Arithmetic => A};
import synthesis.ordered._;
import AST._
import Primitives._

object QFBapa {
}

object QFBAPAtoPATranslator {
  case class IllegalTerm(a: Any) extends Exception(a + " should not be present in the formula to be converted.")

  private implicit def rangeToList[T](r: Traversable[T]): List[T] = r.toList

  def apply(f: Formula) = {
    val sVars = GuessOrdering.setvars(f).toList
    val f1 = rewriteSetRel(f)
    val (at, zs, os) = countCardinalityExpressions(f1)
    val n0 = findSparsenessBound(at - zs - os)
    val n = n0 + os
    val body = reduce(n)(f1)
    f1.print
    println("** #atoms           : " + at)
    println("** #cards = 0       : " + zs)
    println("** #cards <= 1      : " + os)
    println("** d                : " + (at - zs - os))
    println("** sparseness bound : " + n0)
    println("** N                : " + n)

    // TODO why implication ?
    // !And(breakSymmetry(n, sVars).toList ::: nonNegativeCards(n)) || body
    //Or(List(Not(And(breakSymmetry(n, sVars))), body))

    And(body :: nonNegativeCards(n) ::: breakSymmetry(n, sVars).toList)
  }

  private def propVar(k: Int, id: Ident): Formula =
    Ident(IntType, Symbol.beta(k, id)) > 0

  private def natVar(k: Int) =
    Ident(IntType, Symbol.vennSize(k))

  // replace Seteq and Subseteq with Card(...) = 0
  def rewriteSetRel(form: Formula): Formula = form match {
    case True | False => form
    case And(fs) => And(fs map rewriteSetRel)
    case Or(fs) => Or(fs map rewriteSetRel)
    case Not(Predicate(SEQ, List(s1, s2))) =>
      rewriteSetRel(!(s1 subseteq s2) || !(s2 subseteq s1))
    case Not(Predicate(SUBSETEQ, List(s1, s2))) =>
      (s1 ** ~s2).card > 0
    case Not(f) => !rewriteSetRel(f)
    case Predicate(SEQ, List(s1, s2)) =>
      rewriteSetRel((s1 subseteq s2) && (s2 subseteq s1))
    case Predicate(SUBSETEQ, List(s1, s2)) =>
      (s1 ** ~s2).card === 0
    case Predicate(_, _) => form
  }

  // translate BA to PA expression
  // Generate formula of the form
  //    (if st0 then l_k else 0)
  //  where st0 is the result of replacing, in st, the set variables with k-family
  //  of propositional variables, as given by set2prop.
  def ba2pa(setTerm: Term, k: Int): Term = {
    def set2prop(sterm: Term): Formula = sterm match {
      case id@Ident(SetType, _) => propVar(k, id)
      case Lit(EmptySetLit) => False
      case Lit(UniversalSetLit) => True
      case Op(COMPL, List(set)) => !set2prop(set)
      case Op(UNION, sets) => Or(sets map set2prop)
      case Op(INTER, sets) => And(sets map set2prop)
      case _ => throw IllegalTerm(sterm)
    }
    // TODO return if-then-else term
    // IfThenElse(set2prop(setTerm), natVar(k), 0)
    Op(ITE(set2prop(setTerm)), List(natVar(k), 0))
  }

  // reduce QFBAPA formula f to QFPA formula,
  //  introducing only n generic partition cardinality variables
  // pre: formula is in nnf
  def reduce(n: Int) = {
    def reduceFormula(form: Formula): Formula = form match {
      case True | False => form
      case Not(f) => !reduceFormula(f)
      case And(fs) => And(fs map reduceFormula)
      case Or(fs) => Or(fs map reduceFormula)
      case Predicate(c: IntLogical, ts) => Predicate(c, ts map reduceTerm)
      case _ => throw IllegalTerm(form)
    }
    def reduceTerm(term: Term): Term = term match {
      case Op(CARD, List(set)) =>
        Op(ADD, for (k <- (1 to n).toList) yield ba2pa(set, k))
      case Op(c, ts) =>
        Op(c, ts map reduceTerm)
      case Lit(_) | Ident(_, _) => term
    }
    reduceFormula _
  }

  /*
  // TODO not equivalent to ml code -.-
  def countCardinalityExprsByType(f: Formula): (Int, Int) = {
    //var cardIs0count = 0
    //var cardIs1count = 0
    var smallCount = 0
    var bigCount = 0
    def countFormula(form: Formula): Unit = form match {
      case And(fs) => fs foreach countFormula
      case Or(fs) => fs foreach countFormula
      case Predicate(EQ, List(Lit(IntLit(0)), Op(CARD, _)))
              | Predicate(EQ, List(Op(CARD, _), Lit(IntLit(0))))
              | Not(Predicate(EQ, List(Lit(IntLit(1)), Op(CARD, _))))
              | Not(Predicate(EQ, List(Op(CARD, _), Lit(IntLit(1))))) =>
        smallCount += 1
      case Predicate(EQ, List(Lit(IntLit(1)), Op(CARD, _)))
              | Predicate(EQ, List(Op(CARD, _), Lit(IntLit(1)))) =>
        bigCount += 1
      case Predicate(c: IntLogical, ts) => ts foreach countTerm
      // TODO why are seq/subseteq not illegal terms ?
      case True | False | Predicate(SEQ | SUBSETEQ, _) => ()
      case _ => IllegalTerm(form)
    }
    def countTerm(term: Term): Unit = term match {
      case Op(CARD, List(_)) => bigCount += 1
      case Op(_, ts) => ts foreach countTerm
      case _ => ()
    }
    countFormula(f)
    (bigCount, smallCount)
  }
  */

  // Extractor for countCardinalityExpressions
  private object ExCardLessEqual {
    def unapply(form: Formula): Option[(Term, Int)] = form match {
      case Predicate(EQ, List(Lit(IntLit(card)), Op(CARD, List(set)))) => Some((set, card))
      case Predicate(EQ, List(Op(CARD, List(set)), Lit(IntLit(card)))) => Some((set, card))
      case Predicate(GE, List(Lit(IntLit(card)), Op(CARD, List(set)))) => Some((set, card))
      case Predicate(LE, List(Op(CARD, List(set)), Lit(IntLit(card)))) => Some((set, card))
      case Predicate(GT, List(Lit(IntLit(card)), Op(CARD, List(set)))) => Some((set, card - 1))
      case Predicate(LT, List(Op(CARD, List(set)), Lit(IntLit(card)))) => Some((set, card - 1))
      case _ => None
    }
  }


  // TODO not equivalent to ml code -.-
  def countCardinalityExpressions(f: Formula): (Int, Int, Int) = {
    var atoms = 0
    var cardIs0 = 0
    var cardIs1 = 0
    def countFormula(form: Formula): Unit = form match {
      case And(fs) => fs foreach countFormula
      case Or(fs) => fs foreach countFormula
      case ExCardLessEqual(_, 0) => cardIs0 += 1; atoms += 1
      case ExCardLessEqual(_, 1) => cardIs1 += 1; atoms += 1
      case Predicate(c: IntLogical, ts) => ts foreach countTerm
      case True | False => ()
      case _ => IllegalTerm(form)
    }
    def countTerm(term: Term): Unit = term match {
      case Op(CARD, _) => atoms += 1
      case Op(_, ts) => ts foreach countTerm
      case _ => ()
    }
    countFormula(f)
    (atoms, cardIs0, cardIs1)
  }

  // symmetry_breaking predicate says that
  // propositional variables denote a strictly
  // increasing sequence of regions
  val BREAK_SYMMETRY = false

  def breakSymmetry(n: Int, svars: List[Ident]): List[Formula] =
    if (BREAK_SYMMETRY)
      for (i <- (1 to n).toList) yield mkIndexLess(i)(svars)
    else Nil

  def mkIndexLess(i: Int): List[Ident] => Formula = {
    def rek(sets: List[Ident]): Formula = sets match {
      case Nil => True
      case s :: Nil =>
        // prop less
        val varI = propVar(i, s)
        val varI_1 = propVar(i + 1, s)
        !varI && varI_1
      case s :: ss =>
        // prop equal
        val varI = propVar(i, s)
        val varI_1 = propVar(i + 1, s)
        val equal = (!varI && !varI_1) || (varI && varI_1)
        rek(List(s)) || (equal && rek(ss))
    }
    rek _
  }

  // TODO
  def nonNegativeCards(n: Int) =
    for (i <- (1 to n).toList) yield 0 <= natVar(i)

  // compute the largest n such that 2^n <= (n+1)^d
  def findSparsenessBound(d: Int) = {
    // Check if 2^n <= (n+1)^d by taking log of both sides
    def small_n(n: Int) = n * Math.log(2) <= d * Math.log(n + 1)
    def binSearch(low: Int, high: Int): Int = {
      if (high <= low + 1) {
        if (small_n(high))
          high
        else
          low
      } else {
        val mid = (high + low) / 2
        if (small_n(mid))
          binSearch(mid, high)
        else
          binSearch(low, mid)
      }
    }
    if (d <= 3)
      d
    else {
      val a0 = d * Math.log(d)
      val b0 = 2 * d * (1 + Math.log(d))
      binSearch(a0.toInt, b0.toInt)
    }
  }

  def rewriteITEExpression(f: Formula): Formula = {
    // The list which defines the termporary variables for ITE
    // expressions.
    // TODO: There will be multiple occurences of Op(ITE(p, trmLst))
    // in the formula. Hence, this is memonized in the mkITEDef function
    // TODO: How are formula compared?
    var lstDefinitions: List[Formula] = Nil
    var defMap: scala.collection.mutable.Map[Formula, Symbol] = scala.collection.mutable.Map.empty
    var numITE = 0
    def mkITEDef(p: Formula, trmLst: List[Term]): Symbol = defMap.get(p) match {
      case Some(v) => v
      case None => {
        val tf = Symbol.ifThenElse(numITE)
        numITE += 1
        val t1 :: t2 :: Nil = trmLst
        lstDefinitions ::= Or(
          List(
            And(List(p, Predicate(EQ, List(t1, tf)))),
            And(List(Not(p), Predicate(EQ, List(t2, tf))))
            )
          )
        defMap += (p -> tf)
        tf
      }
    }

    def expandITETerm(t: Term): Term = t match {
      case Op(ITE(p), trmLst) => mkITEDef(p, trmLst)
      case Op(op, trmLst) => Op(op, trmLst map expandITETerm)
      case _ => t
    }

    def rec(f: Formula): Formula = f match {
      case And(fLst) => And(fLst map rec)
      case Or(fLst) => Or(fLst map rec)
      case Not(f) => Not(rec(f))
      case Predicate(op: IntLogical, trmLst) => Predicate(op, trmLst map expandITETerm)
      case _ => throw (new IllegalTerm(f))
    }

    val f1 = rec(f) // All ITE terms replaced by fresh variables
    And(f1 :: lstDefinitions)
  }

  // Converts the AST from our to provided Arithmetic AST
  // To pass to the underlying BAPA solver
  def ordFormToArithForm(f: Formula): A.Formula = {

    def mkArithTerm(t: Term): A.Term = t match {
      case Ident(IntType, name) => A.Variable(name.toString)
      case Lit(IntLit(value)) => A.IntLit(value)
      case Op(ADD, trmLst) => A.Plus(trmLst map mkArithTerm)
      case Op(SUB, t1 :: t2 :: Nil) => mkArithTerm(t1 + t2 * (-1))
      // TODO : Make sure that the formula is in PA (linear)
      case Op(MUL, trmLst) => A.Times(trmLst map mkArithTerm)
      case _ => throw (new IllegalTerm(t))
    }

    def mkBiArithPred(op: ((A.Term, A.Term) => A.Predicate), t: Term): A.Predicate = {
      op(mkArithTerm(t), A.IntLit(0))
    }

    def ordPredicateToArithPredicate(op: Logical, terms: List[Term]): A.Formula = {
      val t1 :: t2 :: Nil = terms
      op match {
        case LT => mkBiArithPred(A.GreaterThan, t2 - t1)
        case LE => mkBiArithPred(A.GreaterEqThan, t2 - t1)
        case EQ => mkBiArithPred(A.Equals, t2 - t1)
        case NE => ordFormToArithForm_((t1 < t2) || (t2 < t1))
        case GT => mkBiArithPred(A.GreaterThan, t1 - t2)
        case GE => mkBiArithPred(A.GreaterEqThan, t1 - t2)
        case _ => throw (new IllegalTerm(op))
      }
    }

    def ordFormToArithForm_(f: Formula): A.Formula = f match {
      case And(lst) => A.And(lst map ordFormToArithForm_)
      case Or(lst) => A.Or(lst map ordFormToArithForm_)
      case Not(f) => A.Not(ordFormToArithForm_(f))
      case Predicate(op: IntOperand, lstTerms) => ordPredicateToArithPredicate(op, lstTerms)
      case _ => throw (new IllegalTerm(f))
    }

    val f1 = rewriteITEExpression(f)
    A.normalized(ordFormToArithForm_(f1))
  }

  def callSynth(f: Formula): Unit = {
    var vars = GuessOrdering.intvars(f).toList.map {(x: Ident) => PASynthesis.OutputVar(x.name.toString)}
    val arithFormula = ordFormToArithForm(f)
    A.isSat(arithFormula) match {
      case (None, _) => Console.err.println("Z3 not executed")
      case (Some(true), _) => Console.err.println("Formula Satisfiable");
      case (Some(false), _) => Console.err.println("Formula Unsatisfiable");
    }

    //    val mikaelStyleFormula: PASynthesis.PAFormula = formulaToPAFormula(ordFormToArithForm(f), GuessOrdering.intvars(f).map {_.name.toString}) match {
    //            case Some(f) => f
    //            case None => {
    //              println("predicate contains non-linear arithmetic")
    //              PASynthesis.PAFalse()
    //            }
    //    }
    //    var m1 = PASynthesis.solve(vars, mikaelStyleFormula)
    ()
  }

  def formulaToPAFormula(formula: A.Formula, outVarSet: Set[String]): Option[PASynthesis.PAFormula] = {
    case class EscapeException() extends Exception

    def f2paf(f: A.Formula): PASynthesis.PAFormula = f match {
      case A.And(fs) => PASynthesis.PAConjunction(fs.map(f2paf(_)))
      case A.Or(fs) => PASynthesis.PADisjunction(fs.map(f2paf(_)))
      case A.True() => PASynthesis.PATrue()
      case A.False() => PASynthesis.PAFalse()
      case A.Equals(term, A.IntLit(0)) => PASynthesis.PAEqualZero(makePACombination(term))
      case A.GreaterEqThan(term, A.IntLit(0)) => PASynthesis.PAGreaterEqZero(makePACombination(term))
      case A.GreaterThan(term, A.IntLit(0)) => PASynthesis.PAGreaterZero(makePACombination(term))
      case _ => scala.Predef.error("Unexpected formula in format conversion: " + f)
    }

    def makePACombination(term: A.Term): PASynthesis.PACombination = term match {
      case A.LinearCombination(cstTerm, cstList) => {
        var inVarsAff: List[(Int, PASynthesis.InputVar)] = Nil
        var outVarsAff: List[(Int, PASynthesis.OutputVar)] = Nil

        for ((nme, coef) <- cstList) {
          if (outVarSet.contains(nme)) {
            outVarsAff = (coef, PASynthesis.OutputVar(nme)) :: outVarsAff
          } else {
            inVarsAff = (coef, PASynthesis.InputVar(nme)) :: inVarsAff
          }
        }

        PASynthesis.PACombination(cstTerm, inVarsAff.reverse.removeDuplicates, outVarsAff.reverse.removeDuplicates)
      }
    // case _ => throw EscapeException()
    }

    try {
      Some(f2paf(formula))
    } catch {
      case EscapeException() => None
    }
  }
  /*
 def formulaToAPAFormula2(formula: A.Formula, outVarSet: Set[String]): Option[APAFormula] =
 if(!A.isQuasiLinear(formula, outVarSet)) {
   None
 } else {
   case class EscapeException() extends Exception

   def f2apaf(form: A.Formula): APAFormula = ((form match {
     case A.And(fs) => APAConjunction(fs.map(f2apaf(_)))
     case A.Or(fs) => APADisjunction(fs.map(f2apaf(_)))
     case A.Not(f) => APANegation(f2apaf(f))
     case A.True() => APATrue()
     case A.False() => APAFalse()
     case A.Equals(l,r) => t2apat(l).===(t2apat(r))
     case A.NotEquals(l,r) => APANegation(t2apat(l).===(t2apat(r)))
     case A.LessThan(l,r) => t2apat(l).<(t2apat(r))
     case A.LessEqThan(l,r) => t2apat(l).<=(t2apat(r))
     case A.GreaterThan(l,r) => t2apat(l).>(t2apat(r))
     case A.GreaterEqThan(l,r) => t2apat(l).>=(t2apat(r))
   }):APAFormula).simplified

   def t2apat(term: A.Term): APACombination = ((term match {
     case A.Variable(id) if outVarSet.contains(id) => OutputVar(id).toCombination
     case A.Variable(id) => APACombination(InputVar(id).toInputTerm, Nil)
     case A.IntLit(value) => APACombination(value)
     case A.Neg(t) => t2apat(t).*(-1)
     case A.Plus(ts) => ts.map(t2apat(_)).reduceLeft(_.+(_))
     case A.Minus(t1, t2) => t2apat(t1).-(t2apat(t2))
     case times @ A.Times(ts) => {
       tryInTerm(times) match {
         case Some(apaic) => APACombination(apaic)
         case None => {
           val mapped = ts.map(tryInTerm(_))
           mapped.count(_.isEmpty) match {
             case 0 => scala.Predef.error("Something went wrong.")
             case 1 => {
               val inTerm: APAInputTerm = mapped.filter(_.isDefined).map(_.get).reduceLeft[APAInputTerm]((x:APAInputTerm,y:APAInputTerm) => APAInputMultiplication(x :: y :: Nil).simplified)
               // .get should never fail !
               val outTerm: APACombination = t2apat(ts.find(tryInTerm(_).isEmpty).get)
               outTerm.*(inTerm)
             }
             case _ => throw EscapeException()
           }
         }
       }
     }
     case A.Div(t1, t2) => scala.Predef.error("Div should not occur.")
     case A.Modulo(t1, t2) => scala.Predef.error("Mod should not occur.")
     case A.Min(ts) => scala.Predef.error("Mod should not occur.")
   }):APACombination).simplified

   def tryInTerm(term: A.Term): Option[APAInputTerm] = (term match {
     case A.Variable(id) if outVarSet.contains(id) => None
     case A.Variable(id) => Some(InputVar(id).toInputTerm)
     case A.IntLit(value) => Some(APAInputCombination(value))
     case A.Neg(t) => tryInTerm(t).map(_.*(APAInputCombination(-1)))
     case A.Plus(ts) => {
       val mapped = ts.map(tryInTerm(_))
       mapped.find(_.isEmpty) match {
         case Some(_) => None
         case None => {
           val mappedOK: List[APAInputTerm] = mapped.map(_.get)
           Some(mappedOK.reduceLeft(_.+(_)))
         }
       }
     }
     case A.Minus(t1, t2) => {
       val tt1 = tryInTerm(t1)
       val tt2 = tryInTerm(t2)
       if(tt1.isEmpty || tt2.isEmpty) {
         None
       } else {
         Some(tt1.get.-(tt2.get))
       }
     }
     case A.Times(ts) => {
       val mapped = ts.map(tryInTerm(_))
       mapped.find(_.isEmpty) match {
         case Some(_) => None
         case None => {
           val mappedOK: List[APAInputTerm] = mapped.map(_.get)
           Some(mappedOK.reduceLeft[APAInputTerm]((x:APAInputTerm,y:APAInputTerm) => APAInputMultiplication(x :: y :: Nil).simplified))
         }
       }
     }
     case A.Div(t1, t2) => scala.Predef.error("Div should not occur.")
     case A.Modulo(t1, t2) => scala.Predef.error("Mod should not occur.")
     case A.Min(ts) => scala.Predef.error("Mod should not occur.")
   }).map(_.simplified)

   try {
     Some(f2apaf(formula))
   } catch {
     case EscapeException() => scala.Predef.error("was quasi-linear or not??"); None
   }
 } **/
}

