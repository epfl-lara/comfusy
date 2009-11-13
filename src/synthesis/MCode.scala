package synthesis

/** Minimal Scala code structure to be used as an intermediate
 * representation between PASynthesis.PAProgram and scalac trees. */
trait {
  self: ChooseTransformer =>
  import global._
  import PASynthesis._

  sealed abstract class MStatement
  case class MAssign(varName: String, expr: PATerm) extends MStatement
  case class MIfThenElse(cond: PATerm, then: MStatement, elze: MStatement) extends MStatement
  case class MBlock(stats: List[MStatement]) extends MStatement
  case class MReturn(vars: List[String]) extends MStatement

  def progToMCode(prec: PACondition, prog: PAProgram): MStatement = {
    // we ignore the precondition for now...
 
    MBlock(
      prog.input_assignment.map(ia => MAssign(ia._1.name, ia._2))
      ::: prog.output_assignment.map(oa => MAssign(oa._1.name, oa._2))
      ::: List(MReturn(prog.output_variables.map(_.name)))
    )

  }

  def termToCode(term: PATerm): Tree = term match {
    case PADivision(num, den) => error("XXX") // Literal(Constant(den)) 
    case PAIfThenElse(cond, then, elze) => error("X") // equationToCode 
    case PAMinimum(terms)
    case PAMaximum(terms)
    case PACombination(cst, inAff, outAff)


  }

  def equationToCode(eq: PAEquation): Tree = {
    PADivides
    PAEqualZero
    PAGreaterZero
    PAGreaterEqZero
    PATrue
    PAFalse
  }
}
