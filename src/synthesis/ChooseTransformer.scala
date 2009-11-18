package synthesis

import Arithmetic._

import scala.collection.immutable.Set

import scala.tools.nsc.transform.TypingTransformers

trait ChooseTransformer
  extends TypingTransformers
  with ArithmeticExtractors
  with CodeGeneration {
  self: MainComponent =>
  import global._

  private val SHOWDEBUGINFO = false
  private def dprintln(str: String): Unit = {
    if(SHOWDEBUGINFO)
      println(str)
  }

  private lazy val synthesisDefinitionsModule: Symbol = definitions.getModule("synthesis.Definitions")

  /** The actual rewriting function is the following. */
  def transformChooseCalls(unit: CompilationUnit, emitWarnings: Boolean): Unit =
    unit.body = new ChooseTransformer(unit, emitWarnings).transform(unit.body)

  class ChooseTransformer(unit: CompilationUnit, val emitWarnings: Boolean) extends TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if(synthesisDefinitionsModule == s.symbol && n.toString == "choose") => {
          // SANITY CHECKS
          var foundErrors = false
          // DEBUG reporter.info(a.pos, "here!", true) 
          val Function(funValDefs, funBody) = predicate

          // we check that we're only synthesizing integers, and collect the
          // set of input variables
          for (val valDef <- funValDefs) {
            if(valDef.tpt.tpe != definitions.IntClass.tpe) {
              reporter.error(valDef.pos, "unsupported type in call to synthesizer: " + valDef.tpt.tpe)
              foundErrors = true
            }
          }
          if (foundErrors)
            return a

          // for the record
          val outputVariableList = funValDefs.map(_.name.toString)

          // EXTRACTION
          val (extractedFormula,extractedSymbols) =
           extractFormula(funBody) match {
            case Some((f,s)) => (normalized(f), s.filter((sym: Symbol) => !outputVariableList.contains(sym.name.toString)))
            case None => {
              foundErrors = true
              (False(),Set.empty[Symbol])
            }
          }
          if (foundErrors)
            return a

          dprintln("Corresponding formula: " + extractedFormula)
          dprintln("Symbols in there     : " + extractedSymbols)

          // LINEARIZATION
          val paStyleFormula: PASynthesis.PAFormula = formulaToPAFormula(extractedFormula, Set.empty[String] ++ outputVariableList) match {
            case Some(f) => f
            case None => {
              reporter.error(funBody.pos, "predicate is not in linear arithmetic")
              foundErrors = true
              PASynthesis.PAFalse()
            }
          }
          if (foundErrors) {
            return a
          }

          // We check for uniqueness of the solution.
          if(emitWarnings) {
            val outVars = Set.empty ++ outputVariableList
            val (fcopy,toMap,fromMap) = renameVarSet(extractedFormula, outVars)
            val diseqs: List[Formula] = toMap.map(p => NotEquals(Variable(p._1), Variable(p._2))).toList
            val completeFormula = And(extractedFormula :: fcopy :: diseqs)
            isSat(completeFormula) match {
              case (Some(true), Some(ass)) => {
                var wm = "Synthesis predicate has multiple solutions for variable assignment: "
                wm = wm + ass.keys.filter(k => !toMap.keys.contains(k) && !fromMap.keys.contains(k)).toList.map(k => k + " = " + ass(k)).mkString(", ")
                wm = wm + "\n"
                wm = wm + "  Solution 1: " + outVars.toList.map(k => k + " = " + ass(k)).mkString(", ") + "\n"
                wm = wm + "  Solution 2: " + outVars.toList.map(k => k + " = " + ass(toMap(k))).mkString(", ") + "\n"
                reporter.info(a.pos, wm, true)
              }
              case (Some(false), _) => ; // desirable: solution is always unique if it exists
              case (_,_) => reporter.info(a.pos, "Synthesis predicate may not always have a unique solution (decision procedure did not respond).", true)
            }
          }

          dprintln("Mikael-Style formula : " + paStyleFormula)
          val (paPrec,paProg) = PASynthesis.solve(outputVariableList.map(PASynthesis.OutputVar(_)), paStyleFormula)
          dprintln("Precondition         : " + paPrec)
          dprintln("Program              : " + paProg)

          // We try to falsify the pre-condition.
          if(emitWarnings) {
            isSat(Not(conditionToFormula(paPrec))) match {
              case (Some(true), Some(ass)) => {
                reporter.info(a.pos, "Synthesis predicate is not satisfiable for variable assignment: " + ass.map(p => p._1 + " = " + p._2).mkString(", "), true)

              }
              case (Some(false), _) => ;
              case (_,_) => reporter.info(a.pos, "Synthesis predicate may not always be satisfiable (decision procedure did not respond).", true)
            }
          }
          
          // CODE GENERATION
          var initialMap: SymbolMap = Map.empty
          extractedSymbols.foreach(sym => {
            initialMap = initialMap + (sym.name.toString -> sym)
          })
          val codeGen = new CodeGenerator(unit, currentOwner, initialMap, emitWarnings, a.pos)
          typer.typed(atOwner(currentOwner) {
            codeGen.programToCode(paPrec, paProg) 
          })
        }
        case _ => super.transform(tree)
      }
    }

    // tries to extract an arithmetic formula from the code.
    def extractFormula(tree: Tree): Option[(Formula,Set[Symbol])] = {
      var extractedSymbols: Set[Symbol] = Set.empty
      case class EscapeException() extends Exception

      def ef(t: Tree): Formula = t match {
        case ExTrueLiteral() => True()
        case ExFalseLiteral() => False()
        case ExAnd(l,r) => And(ef(l), ef(r))
        case ExOr(l,r) => Or(ef(l), ef(r))
        case ExNot(f) => Not(ef(f))
        case ExEquals(l,r) => Equals(et(l), et(r))
        case ExNotEquals(l,r) => NotEquals(et(l), et(r))
        case ExLessThan(l,r) => LessThan(et(l), et(r))
        case ExLessEqThan(l,r) => LessEqThan(et(l), et(r))
        case ExGreaterThan(l,r) => GreaterThan(et(l), et(r))
        case ExGreaterEqThan(l,r) => GreaterEqThan(et(l), et(r))
        case _ => {
          reporter.error(t.pos, "invalid expression in sythesis predicate")
          throw EscapeException()
        }
      }

      def et(t: Tree): Term = t match {
        case ExIntLiteral(value) => IntLit(value)
        case ExIntIdentifier(id) => {
          extractedSymbols = extractedSymbols + id.symbol
          Variable(id.toString)
        }
        case ExPlus(l,r) => Plus(et(l), et(r))
        case ExMinus(l,r) => Minus(et(l), et(r))
        case ExTimes(l,r) => Times(et(l), et(r))
        // case ExDiv(l,r) => Div(et(l), et(r))
        // case ExModulo(l,r) => Modulo(et(l), et(r))
        case ExNeg(t) => Neg(et(t))
        case _ => {
          reporter.error(t.pos, "invalid term in synthesis predicate")
          throw EscapeException()
        }
      }

      try {
        val res = ef(tree)
        Some((res,extractedSymbols))
      } catch {
        case EscapeException() => None
      }
    }

    // tries to convert a formula to Mikael's format. Returns None if one of
    // the predicates contains a non-linear term.
    def formulaToPAFormula(formula: Formula, outVarSet: Set[String]): Option[PASynthesis.PAFormula] = {
      case class EscapeException() extends Exception

      def f2paf(f: Formula): PASynthesis.PAFormula = f match {
        case And(fs) => PASynthesis.PAConjunction(fs.map(f2paf(_)))
        case Or(fs) => PASynthesis.PADisjunction(fs.map(f2paf(_)))
        case True() => PASynthesis.PATrue()
        case False() => PASynthesis.PAFalse()
        case Equals(term, IntLit(0)) => PASynthesis.PAEqualZero(makePACombination(term))
        case GreaterEqThan(term, IntLit(0)) => PASynthesis.PAGreaterEqZero(makePACombination(term))
        case _ => scala.Predef.error("Unexpected formula in format conversion: " + f)
      }

      def makePACombination(term: Term): PASynthesis.PACombination = term match {
        case LinearCombination(cstTerm, cstList) => {
          var inVarsAff:  List[(Int,PASynthesis.InputVar)] = Nil
          var outVarsAff: List[(Int,PASynthesis.OutputVar)] = Nil

          for((nme,coef) <- cstList) {
            if(outVarSet.contains(nme)) {
              outVarsAff = (coef,PASynthesis.OutputVar(nme)) :: outVarsAff
}
            else
{
              inVarsAff = (coef,PASynthesis.InputVar(nme)) :: inVarsAff
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
  }

  def conditionToFormula(cond: PASynthesis.PACondition): Formula = {
    import PASynthesis._

    def f2f(f: PAFormula): Formula = f match {
      case PAConjunction(fs) => And(fs.map(f2f(_)))
      case PADisjunction(fs) => Or(fs.map(f2f(_)))
      case PADivides(coef, comb) => Equals(IntLit(0), Modulo(t2t(comb), IntLit(coef)))
      case PAEqualZero(comb) => Equals(IntLit(0), t2t(comb))
      case PAGreaterZero(comb) => LessThan(IntLit(0), t2t(comb))
      case PAGreaterEqZero(comb) => LessEqThan(IntLit(0), t2t(comb))
      case PATrue() => True()
      case PAFalse() => False()
    }

    def t2t(t: PATerm): Term = t match {
      case PACombination(coef, ias, oas) => {
        Plus(IntLit(coef) ::
          ias.map(ia => Times(IntLit(ia._1) :: Variable(ia._2.name) :: Nil)) :::
          oas.map(oa => Times(IntLit(oa._1) :: Variable(oa._2.name) :: Nil)))
      }
      case PADivision(pac, coef) => {
        Div(t2t(pac), IntLit(coef))
        /* val num = t2t(pac)
        val den = IntLit(coef)
        Div(
          Minus(
            num,
            Modulo(
              Plus(den :: Modulo(num, den) :: Nil),
              den)),
          den) */
      }
      case PAMinimum(ts) => Min(ts.map(t2t(_)))
      case PAMaximum(ts) => Neg(Min(ts.map(tr => Neg(t2t(tr)))))
    }

    val inAss = cond.input_assignment.map(ia => {
      Equals(Variable(ia._1.name), t2t(ia._2))
    })
    val out = normalized(And(f2f(cond.global_condition) :: inAss))
    //println(out)
    out
  }

}
