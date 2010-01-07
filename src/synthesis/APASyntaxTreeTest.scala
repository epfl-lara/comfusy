package synthesis

import org.scalatest._
import org.scalatest.matchers._

class APASyntaxTreeTest extends Spec with ShouldMatchers {
  def O(name: String) = OutputVar(name)
  def I(name: String) = InputVar(name)
  implicit def OutputVarToPACombination(o: OutputVar):APACombination = APACombination(o)
  implicit def InputTermConvert(i: ConvertibleToInputTerm):APAInputTerm = i.toInputTerm()
  implicit def IntegerToPACombination(k: Int):APAInputCombination = APAInputCombination(k)
  implicit def InputToPACombination(k: APAInputTerm):APACombination = APACombination(k)

  val x = O("x")
  val x1 = O("x1")
  val y = O("y")
  val y1 = O("y1")
  val z = O("z")
  
  val b = I("b")
  val x0 = I("x0")
  val c = I("c")
  val d = I("d")
  
  it("should get the right equations from a general formula") {
    val pac = (x >= 0) && ((x >= 1) || ((y+z) <= 0)) && ((x < 1) || ((y-z) <= 0))
    pac.getEquations.toList should equal (
      List((x >= 0), (x >= 1),     (x < 1)) ::
      List((x >= 0), (x >= 1),     ((y-z) <= 0)) ::
      List((x >= 0), ((y+z) <= 0), (x < 1)) ::
      List((x >= 0), ((y+z) <= 0), ((y-z) <= 0)) ::
      Nil
    )
  }
  it("should be able to extract equalities from a formula") {
    val eq1 = (x+y === b).asInstanceOf[APAEqualZero]
    val eq2 = (x-y === z+c).asInstanceOf[APAEqualZero]
    val ineq0 = (x > z-c)
    val ineq1 = x < y
    val ineq2 = x > y
    val pac = eq1 && eq2 && ineq0 && (ineq1 || ineq2)

    val fs  = pac.getLazyEquations
    fs.eqs should equal (eq1::eq2::Nil)
    fs.noneqs should equal (ineq0::Nil)
    fs.remaining.head should equal (FormulaSplit(Nil, ineq1::Nil, Stream.empty))
    fs.remaining.tail.head should equal (FormulaSplit(Nil, ineq2::Nil, Stream.empty))
    fs.remaining.tail.tail should be ('empty)
  }
}
