package synthesis
package ordered

import synthesis.bapa.{ASTBAPASyn => BSyn}
import synthesis.ordered.AST._
import synthesis.ordered.Primitives._
import synthesis.{Arithmetic => A}

object BapaConverter {
  def solve(inSetVars: List[Symbol], outSetVars: List[Symbol], inTermVars: List[Symbol], outTermVars: List[Symbol], f: Formula) = {
    val BC = new BapaConverter

    //    def findSetLits( trm : Term ) : Set[Symbol] = {
    //        case Ident(s) => Set(s)
    //        case Lit(_) => Set.empty
    //        case Op(
    //
    //    def getSetVars(f : Formula) : Set[Symbol] = f match {
    //      case And(frmlLst) => (Set() ++ frmlLst).flatMap(getSetVars)
    //      case Or(frmlLst) => (Set() ++ frmlLst).flatMap(getSetVars)
    //      case Not(frml) => getSetVars(frml)
    //      case Predicate( _, terms ) => terms.flatMap(findSetLits)
    //    }
    //
    //    def getElemVars(f : Formula) : Set[Symbol] = f match {
    //      case And(frmlLst) => (Set() ++ frmlLst).flatMap(getElemVars)
    //      case Or(frmlLst) => (Set() ++ frmlLst).flatMap(getElemVars)
    //      case Not(frml) => getElemVars(frml)
    //      case Predicate( _, terms ) => terms.flatMap(findIntLits)
    //    }

    //    println("SetVars = " + (inSetVars ++ outSetVars) + "\nTermVars = " + (inTermVars ++ outTermVars))
    BC.solve(inSetVars map (_.name), outSetVars map (_.name), inTermVars map (_.name), outTermVars map (_.name), f)
  }
}

class BapaConverter {
  // import global._

  case class IllegalTerm(a: Any) extends Exception(a + " should not be present in the formula to be converted.")

  private def ordPAIntToBapaPAInt(i: Term): BSyn.PAInt = i match {
    case Ident(IntType, s) => BSyn.IntVar(s.name)
    case Lit(IntLit(lit)) => BSyn.IntConst(lit)

    case Op(ADD, hd :: Nil) => ordPAIntToBapaPAInt(hd)
    case Op(ADD, hd :: rest) => BSyn.Plus(ordPAIntToBapaPAInt(hd), ordPAIntToBapaPAInt(Op(ADD, rest)))
    case Op(SUB, hd :: tl :: Nil) => BSyn.Plus(ordPAIntToBapaPAInt(hd), BSyn.Times(-1, ordPAIntToBapaPAInt(tl)))
    case Op(CARD, hd :: Nil) => BSyn.Card(ordBASettoBapaBASet(hd))

    // TODO: Only two cases of Multiplication considered
    case Op(MUL, hd :: Lit(IntLit(c)) :: Nil) => BSyn.Times(c, ordPAIntToBapaPAInt(hd))
    case Op(MUL, Lit(IntLit(c)) :: tl :: Nil) => BSyn.Times(c, ordPAIntToBapaPAInt(tl))
    case _ => throw (new IllegalTerm(i))

  // case TermVar(i: String) => BSyn.IntVar(i)
  // case IntConst(c: Int) => BSyn.IntConst(c)
  // case Plus(i1: PAInt, i2: PAInt) => BSyn.Plus(ordPAIntToBapaPAInt(i1), ordPAIntToBapaPAInt(i2))
  // case Times(c: Int, i2: PAInt) =>  BSyn.Times(c, ordPAIntToBapaPAInt(i2))
  }

  private def ordBASettoBapaBASet(s: Term): BSyn.BASet = s match {
    case Ident(SetType, s) => BSyn.SetVar(s.name)
    case Lit(EmptySetLit) => BSyn.EmptySet
    // case Lit(UniversalSetLit) => BSyn.UnivSet

    case Op(UNION, hd :: Nil) => ordBASettoBapaBASet(hd)
    case Op(UNION, hd :: rest) => BSyn.Intersec(ordBASettoBapaBASet(hd), BSyn.Compl(ordBASettoBapaBASet(Op(UNION, rest))))

    case Op(INTER, hd :: Nil) => ordBASettoBapaBASet(hd)
    case Op(INTER, hd :: rest) => BSyn.Intersec(ordBASettoBapaBASet(hd), ordBASettoBapaBASet(Op(INTER, rest)))

    case Op(MINUS, hd :: tl :: Nil) => BSyn.Intersec(ordBASettoBapaBASet(hd), BSyn.Compl(ordBASettoBapaBASet(tl)))

    case Op(COMPL, hd :: Nil) => BSyn.Compl(ordBASettoBapaBASet(hd))
    case _ => throw (new IllegalTerm(s))

  // case SetVar(s:String) => BSyn.SetVar(s)
  // case EmptySet => BSyn.EmptySet
  // case UnivSet => BSyn.UnivSet
  // case Union(s1: BASet, s2: BASet) => BSyn.Union( ordBASettoBapaBASet(s1), ordBASettoBapaBASet(s2))
  // case Intersec(s1: BASet, s2: BASet) => BSyn.Intersec(ordBASettoBapaBASet(s1), ordBASettoBapaBASet(s2))
  // case Compl(s: BASet) => BSyn.Compl(ordBASettoBapaBASet(s))
  // case Take(n1: PAInt, s1: BASet) => throw(new IllegalTerm(s))
  }

  private def ordToBapaAtom(l: Logical, trmLst: List[Term]): BSyn.Formula = {
    val (hd :: tl :: rest) = trmLst
    l match {
      case LT => BSyn.And(BSyn.Not(ordToBapaAtom(EQ, trmLst)), ordToBapaAtom(LE, trmLst))
      case LE => BSyn.FAtom(BSyn.IntLessEqual(ordPAIntToBapaPAInt(hd), ordPAIntToBapaPAInt(tl)))
      case EQ => BSyn.FAtom(BSyn.IntEqual(ordPAIntToBapaPAInt(hd), ordPAIntToBapaPAInt(tl)))
      case NE => BSyn.Not(BSyn.FAtom(BSyn.IntEqual(ordPAIntToBapaPAInt(hd), ordPAIntToBapaPAInt(tl))))
      case GT => BSyn.Not(BSyn.FAtom(BSyn.IntLessEqual(ordPAIntToBapaPAInt(hd), ordPAIntToBapaPAInt(tl))))
      case GE => BSyn.Or(ordToBapaAtom(EQ, trmLst), ordToBapaAtom(GT, trmLst))

      case SEQ => BSyn.FAtom(BSyn.SetEqual(ordBASettoBapaBASet(hd), ordBASettoBapaBASet(tl)))
      case SLT => throw (new IllegalTerm(Predicate(l, trmLst)))
      case SELEM => throw (new IllegalTerm(Predicate(l, trmLst)))
      case SUBSETEQ => BSyn.Or(
        BSyn.FAtom(BSyn.SetSubset(ordBASettoBapaBASet(hd), ordBASettoBapaBASet(tl))),
        ordToBapaAtom(SEQ, trmLst)
        )

    // case TermEqual(i1: PAInt, i2: PAInt) => BSyn.IntEqual(ordPAIntToBapaPAInt(i1), ordPAIntToBapaPAInt(i2))
    // case TermLessEqual(i1: PAInt, i2: PAInt) => BSyn.IntLessEqual(ordPAIntToBapaPAInt(i1), ordPAIntToBapaPAInt(i2))
    // case TermIsInt(i1: PAInt) => throw(new IllegalTerm(a))
    // case SetEqual(s1: BASet, s2: BASet) => BSyn.SetEqual( ordBASettoBapaBASet(s1), ordBASettoBapaBASet(s2))
    // case SetLess(s1: BASet, s2: BASet) => throw(new IllegalTerm(a))
    // case SetElem(t1: PAInt, s2: BASet) => throw(new IllegalTerm(a))
    // case SetIsInfinite(s1: BASet) => throw(new IllegalTerm(a))
    // case SetCard(s1: BASet, t1: PAInt) => BSyn.IntEqual( BSyn.Card(ordBASettoBapaBASet(s1)), ordPAIntToBapaPAInt(t1))
    // case SetInf(s1: BASet, t1: PAInt) => throw(new IllegalTerm(a))
    // case SetSup(s1: BASet, t1: PAInt) => throw(new IllegalTerm(a))
    }
  }

  def ord2bapa(f: Formula): BSyn.Formula = f match {
    case And(Nil) => throw (new IllegalTerm(f))
    case And(hd :: frmlList) => frmlList.foldLeft(ord2bapa(hd))({(x: BSyn.Formula, y: Formula) => BSyn.And(x, ord2bapa(y))})

    case Or(Nil) => throw (new IllegalTerm(f))
    case Or(hd :: frmlList) => frmlList.foldLeft(ord2bapa(hd))({(x: BSyn.Formula, y: Formula) => BSyn.Or(x, ord2bapa(y))})
    case Not(f1) => BSyn.Not(ord2bapa(f1))
    case Predicate(c, trmLst) => ordToBapaAtom(c, trmLst)
    case True => throw (new IllegalTerm(f))
    case False => throw (new IllegalTerm(f))
  }

  /* May need to export this part
          into Choose Transformer. */
  def solve(
          inSetVar: List[String],
          outSetVar: List[String],
          inTermVar: List[String],
          outTermVar: List[String],
          f: Formula) = {
    // FIXME: Code copied from the ChooseTransformer.java
    // tries to convert a formula to Mikael's format. Returns None if one of
    // the predicates contains a non-linear term.
    def formulaToPAFormula(formula: A.Formula, outVarSet: Set[String]): Option[PASynthesis.PAFormula] = {
      case class EscapeException() extends Exception

      def f2paf(f: A.Formula): PASynthesis.PAFormula = f match {
        case A.And(fs) => PASynthesis.PAConjunction(fs.map(f2paf(_)))
        case A.Or(fs) => PASynthesis.PADisjunction(fs.map(f2paf(_)))
        case A.True() => PASynthesis.PATrue()
        case A.False() => PASynthesis.PAFalse()
        case A.Equals(term, A.IntLit(0)) => PASynthesis.PAEqualZero(makePACombination(term))
        case A.GreaterEqThan(term, A.IntLit(0)) => PASynthesis.PAGreaterEqZero(makePACombination(term))
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
        case _ => throw EscapeException()
      }

      try {
        Some(f2paf(formula))
      } catch {
        case EscapeException() => None
      }
    }

    val bapaForm = ord2bapa(f)
    val rStyleForm = BSyn.Task(inSetVar, outSetVar, inTermVar, outTermVar, bapaForm)
    val (preCardAssigns, frmForSynthesis, linOutVars, setAssignments) = bapa.Algorithm.solve(rStyleForm, true)
    val pStyle = A.normalized(bapa.ASTBAPASyn.bapaFormToArithForm(frmForSynthesis))
    val mStyle: PASynthesis.PAFormula = formulaToPAFormula(pStyle, Set.empty[String] ++ linOutVars) match {
      case Some(f) => f
      case None => {
        // reporter.error(funBody.pos, "predicate contains non-linear arithmetic")
        PASynthesis.PAFalse()
      }
    }
    val (paPrec, paProg) = PASynthesis.solve(linOutVars.map(PASynthesis.OutputVar(_)), mStyle)
    (preCardAssigns, mStyle, paPrec, paProg, setAssignments)
  }
}
