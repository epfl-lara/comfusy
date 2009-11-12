package synthesis

import Arithmetic._

import scala.collection.immutable.Set

import scala.tools.nsc.transform.TypingTransformers

trait ChooseTransformer
  extends TypingTransformers
  with ArithmeticExtractors {
  self: MainComponent =>
  import global._

  private lazy val synthesisDefinitionsModule: Symbol = definitions.getModule("synthesis.Definitions")
  private lazy val unsatConstraintsException: Symbol = definitions.getClass("synthesis.Definitions.UnsatisfiableConstraint")

  /** The actual rewriting function is the following. */
  def transformChooseCalls(unit: CompilationUnit): Unit =
    unit.body = new ChooseTransformer(unit).transform(unit.body)

  class ChooseTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {
    override def transform(tree: Tree): Tree = {
      tree match {
        case a @ Apply(TypeApply(Select(s: Select, n), _), rhs @ List(predicate: Function)) if(synthesisDefinitionsModule == s.symbol && n.toString == "choose") => {
          // SANITY CHECKS
          var foundErrors = false
          reporter.info(a.pos, "here!", true) 
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
          val extractedFormula: Formula = extractFormula(funBody) match {
            case Some(f) => normalized(f)
            case None => {
              foundErrors = true
              False() // arbitrary, but hey.
            }
          }
          if (foundErrors)
            return a

          println("Corresponding formula: " + extractedFormula)

          // LINEARIZATION
          val paStyleFormula: PASynthesis.PAFormula = formulaToPAFormula(extractedFormula, Set.empty[String] ++ outputVariableList) match {
            case Some(f) => f
            case None => {
              reporter.error(funBody.pos, "predicate is not in linear arithmetic")
              foundErrors = true
              PASynthesis.PAFalse()
            }
          }
          if (foundErrors)
            return a

          println("Mikael-Style formula : " + paStyleFormula)

          val (paPrec,paProg) = PASynthesis.solve(outputVariableList.map(PASynthesis.OutputVar(_)), paStyleFormula)

          println("Precondition         : " + paPrec)
          println("Program              : " + paProg)

          println("MCode                : " + MCode.progToMCode(paPrec,paProg))
          
          // CODE GENERATION
          // we prepare a fresh variable symbol for each output var.
          val outputVariableSymbols: List[Symbol] = funValDefs.map(fvd => {
            currentOwner.newValue(fvd.pos, unit.fresh.newName(fvd.pos, "out")).setInfo(definitions.IntClass.tpe)
          })

          // STARTING TO PUT THE CODE TOGETHER HERE !
          // Throw(New(Ident(unsatConstraintsException), List(Nil))) 
          typer.typed(atOwner(currentOwner) {
            Block(
              outputVariableSymbols.map(ovs => {
                ValDef(ovs, Literal(42))
              })
              //:: Nil
              ,
              if(outputVariableSymbols.length == 1) {
                Ident(outputVariableSymbols(0))
              } else {
                New(
                  TypeTree(definitions.tupleType(funValDefs.map(x => definitions.IntClass.tpe))),
                  List(outputVariableSymbols.map(ovs => Ident(ovs)))
                )
              }
            )
          })
        }
        case _ => super.transform(tree)
      }
    }

    // tries to extract an arithmetic formula from the code.
    def extractFormula(tree: Tree): Option[Formula] = {
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
        case ExIntIdentifier(id) => Variable(id.toString) //Variable("'"+id.toString+"'")
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
        Some(ef(tree))
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
}
