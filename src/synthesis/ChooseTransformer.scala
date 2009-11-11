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
          val extractedExpression: Formula = funBody match {
            case ExTrueLiteral() => True()
            case ExFalseLiteral() => False()
            case ExEquals(l,r) => {
              println("HERE I GOT IT!!!")
              println(l)
              println(r)
              null
            }
            case _ => {
              reporter.error(funBody.pos, "expression in synthesis predicate is not linear arithmetic")
              foundErrors = true
              False() // arbitrary, but hey.
            }
          }
          if (foundErrors)
            return a

          println("Corresponding formula: " + extractedExpression)

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
  }
}
