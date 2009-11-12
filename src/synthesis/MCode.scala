package synthesis

/** Minimal Scala code structure to be used as an intermediate
 * representation between PASynthesis.PAProgram and scalac trees. */
object MCode {
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
}
