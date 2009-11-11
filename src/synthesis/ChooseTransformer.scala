package synthesis

import Arithmetic._

import scala.tools.nsc.transform.TypingTransformers

trait ChooseTransformer
  extends TypingTransformers
  with ArithmeticExtractors {
  self: MainComponent =>
  import global._

  private lazy val synthesisDefinitionsModule: Symbol = definitions.getModule("synthesis.Definitions")

  private def isChooseFunction(symbol: Symbol): Boolean = {
    symbol == synthesisDefinitionsModule.tpe.decl("choose")
  }

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

          // we check that we're only synthesizing integers
          for (val valDef <- funValDefs) {
            if(valDef.tpt.tpe != definitions.IntClass.tpe) {
              reporter.error(valDef.pos, "unsupported type in call to synthesizer: " + valDef.tpt.tpe)
              foundErrors = true
            }
          }
          if (foundErrors)
            return a

          // EXTRACTIONS
          val extractedFormula: Formula = extractFormula(funBody) match {
            case Some(f) => f
            case None => {
              foundErrors = true
              False() // arbitrary, but hey.
            }
          }
          if (foundErrors)
            return a

          println("Corresponding formula: " + extractedFormula)

          // CODE GENERATION
          // currently, generates a tuple of the right size containing only zeroes :)
          if(funValDefs.length == 1) {
            // special case for only one var:
            typer.typed(atOwner(currentOwner) {
              Literal(0)
            })
          } else {
            // all other cases.
            typer.typed(atOwner(currentOwner) {
              Block(List(Literal(42)), 
              New(TypeTree(definitions.tupleType(funValDefs.map(x => definitions.IntClass.tpe))),
                List(funValDefs.map(x => Literal(0)))))
            })
          }
        }
        case _ => super.transform(tree)
      }
    }

    def extractFormula(tree: Tree): Option[Formula] = {
      case class EscapeException() extends Exception

      def ef(t: Tree): Formula = t match {
        case ExTrueLiteral() => True()
        case ExFalseLiteral() => False()
        case ExAnd(l,r) => And(List(ef(l), ef(r)))
        case ExOr(l,r) => Or(List(ef(l), ef(r)))
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
        case ExIntIdentifier(id) => Variable("'"+id.toString+"'")
        case ExPlus(l,r) => Plus(et(l), et(r))
        case ExMinus(l,r) => Minus(et(l), et(r))
        case ExTimes(l,r) => Times(et(l), et(r))
        case ExDiv(l,r) => Div(et(l), et(r))
        case ExModulo(l,r) => Modulo(et(l), et(r))
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
  }
}
