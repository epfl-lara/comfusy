package synthesis

import org.scalatest._
import org.scalatest.matchers._

class PASynthesisTest extends Spec with ShouldMatchers {
  import PASynthesis._
  def O(name: String) = PASynthesis.OutputVar(name)
  def I(name: String) = PASynthesis.InputVar(name)
  implicit def OutputVarToPACombination(o: OutputVar):PACombination = PACombination(o)
  implicit def InputVarToPACombination(i: InputVar):PACombination = PACombination(i)
  implicit def IntegerToPACombination(k: Int):PACombination = PACombination(k)

  val x = O("x")
  val x1 = O("x1")
  val y = O("y")
  val y1 = O("y1")
  val z = O("z")
  
  val b = I("b")
  val x0 = I("x0")
  val c = I("c")
  val d = I("d")
  
  describe("Creator of new variable") {
    it("should create a variable not contained in a list") {
      val l_output_vars = x::x1::y::y1::Nil
      val v = PASynthesis.newOutputVariable(l_output_vars)
      l_output_vars should not contain v
    }
  }
  
  describe("Common functions") {
    it("should compute the GCD of a list") {
      Common.gcdlist((-18)::12::0::36::Nil) should equal (6)
    }
    it("specialMod") {
      Common.smod(10, 7) should equal(3)
      Common.smod(11, 7) should equal(-3)
      Common.smod(14, 7) should equal(0)
      Common.smod(3, 8) should equal(3)
      Common.smod(4, 8) should equal(-4)
      Common.smod(5, 8) should equal(-3)
      Common.smod(-10, 7) should equal(-3)
      Common.smod(-11, 7) should equal(3)
      Common.smod(-14, 7) should equal(0)
      Common.smod(-3, 8) should equal(-3)
      Common.smod(-4, 8) should equal(-4)
      Common.smod(-5, 8) should equal(3)
    }
  }
  
  describe("PACombinations") {
    it("Should simplify expressions") {
      val pac = PACombination(0, (1, b)::(2, c)::(-2, b)::Nil, (2, x)::(1, y)::(-2, x)::Nil).simplified
      pac should equal (PACombination(0, (-1, b)::(2, c)::Nil, (1, y)::Nil))
    }
    it("Should handle combination sums") {
      val pac1 = PACombination(-2, (1, b)::(2,  c)::Nil, (2, x)::(1,  y)::(1,  x)::Nil)
      val pac2 = PACombination(5, (2, b)::(-5, c)::Nil,  (2, y)::(-7, x)::(-3, y)::Nil)
      (pac1 + pac2) should equal (
                 PACombination(3, (3, b)::(-3, c)::Nil, (-4, x)::Nil))
    }
    it("Should handle integer divisions") {
      val pac1 = PACombination(-2, (2, b)::(6, c)::Nil, (-4, x)::(-7, y)::Nil)
      (pac1/3).simplified should equal(
                 PACombination(0, (2, c)::Nil, (-1, x)::(-2, y)::Nil))
    }
    it("Should handle integer multiplication") {
      val pac1 = PACombination(-2, (2, b)::(6, c)::Nil, (-4, x)::(-7, y)::Nil)
      (pac1*3).simplified should equal(
                 PACombination(-6, (6, b)::(18, c)::Nil, (-12, x)::(-21, y)::Nil))
    }
    it("Should normalize when asked") {
      val pac = PACombination(5, (15,  c)::(5, b)::Nil, (-5, x)::(-25,  y)::Nil)
      pac.normalized.simplified should equal (
                PACombination(1, (1,  b)::(3, c)::Nil, (-1, x)::(-5,  y)::Nil))
    }
    it("Should replace variables by expressions") {
      val pac_before =    PACombination(5, (3, c)::(-5, b)::Nil, (5, y)::(-4, x)::(-2, y)::Nil)
      val pac_replace_y = PACombination(1, (4, c)::(-1, b)::Nil, (3, x)::Nil)
      pac_before.replace(y, pac_replace_y) should equal (
                          PACombination(8, (-8, b)::(15, c)::Nil, (5, x)::Nil)
      )
    }
    it("Should compute special modulos") {
      val pac = PACombination(5, (15,  c)::(5, b)::Nil, (-5, x)::(-25,  y)::Nil)
      (pac %% 3) should equal (PACombination(-1, (-1, b)::Nil, (1, x)::(-1, y)::Nil))
    }
    it("Should handle tuple addition") {
      val pac = PACombination(5, (15,  c)::(5, b)::Nil, (-5, x)::(-25,  y)::Nil)
      (pac + (5, y)) should equal (PACombination(5, (5,  b)::(15, c)::Nil, (-5, x)::(-20,  y)::Nil))
    }
    it("Should render expressions correctly") {
      PACombination(0, Nil, Nil).toNiceString should equal ("0")
      PACombination(5, Nil, Nil).toNiceString should equal ("5")
      PACombination(5, (2, b)::Nil, Nil).toNiceString should equal ("5+2*b")
      PACombination(5, (-2, b)::Nil, Nil).toNiceString should equal ("5-2*b")
      PACombination(0, (2, b)::Nil, Nil).toNiceString should equal ("2*b")
      PACombination(0, (-2, b)::Nil, Nil).toNiceString should equal ("-2*b")
      PACombination(0, (-1, b)::(-1, c)::Nil, Nil).toNiceString should equal ("-b-c")
      PACombination(5, Nil, (2, x)::Nil).toNiceString should equal ("5+2*x")
      PACombination(5, Nil, (-2, x)::Nil).toNiceString should equal ("5-2*x")
      PACombination(0, Nil, (2, x)::Nil).toNiceString should equal ("2*x")
      PACombination(0, Nil, (-2, x)::Nil).toNiceString should equal ("-2*x")
      PACombination(0, Nil, (-1, x)::(-1, y)::Nil).toNiceString should equal ("-x-y")
    }
  }
  describe("PASynthesis instance") {
    it("should solve underconstrained equations") {
      val pac = b + x*10 + y*14 + z*35 === 0
      val solution = PASynthesis.solve("underconstrained", pac)
      solution._1 should equal (PACondition(Nil, PATrue()))
      println(solution._2)
    }
    it("should solve normally constrained equations 1") {
      val pac1 = b + x*2 ===0
      val solution = PASynthesis.solve("constrained1", pac1)
      solution._1 should equal (PACondition(Nil, PADivides(2, b)))
      solution._2.input_assignment should equal ((x0, PADivision(b, 2))::Nil)
      solution._2.output_assignment should equal ((x, -x0)::Nil)
      println(solution._2)
    }
    it("should solve normally constrained equations 2") {
      val pac1 = b + x*10 + y*14 + z*35
      val pac2 = c*2 -x*3 +z*35
      val pac3 = ((-b)-(x*5)) + z*8
      val solution = PASynthesis.solve(PAEqualZero(pac1)::PAEqualZero(pac2)::PAEqualZero(pac3)::Nil)
      solution._1 should equal (PACondition((x0,PADivision(PACombination(0,(1,b)::(-145,c)::Nil,Nil),7))::Nil,
                                            PAConjunction(PADivides(302,PACombination(0,List((-1,b), (47,c), (151,x0)),Nil))::
                                                          PADivides(7,PACombination(0,List((1,b), (-145,c)),Nil))::Nil)))
      println(solution._2)
    }
    it("should solve overconstrained equations") {
      val x0 = InputVar("x0")
      val pac1 = b+(x*2) === 0
      val pac2 = (c*2)-(x*3) === 0
      val solution = PASynthesis.solve("overconstrained", pac1, pac2)
      println(solution._1)
      println(solution._2)
      solution._1 should equal (PACondition((x0,PADivision(PACombination(b),2))::Nil,
              PAConjunction(PAEqualZero(PACombination(0,List((2,c), (3,x0)),List()))::PADivides(2,PACombination(b))::Nil)))
    }
    it("should solve trivial unsatisfiable equations") {
      val pac1 = b+(x*2) === 0
      val pac2 = b+(x*2) === 1
      val solution = PASynthesis.solve("unsatisfiable", pac1, pac2)
      //solution._1 should equal (PAFalse())
      println(solution._2)
      // TODO: how to detect that this is not satisfiable ?
    }
    it("should not care about equation duplicates") {
      val eq1 = b-x === 0
      val solution = PASynthesis.solve(eq1::eq1::eq1::eq1::eq1::Nil)
      solution._1.global_condition should equal (PATrue())
      solution._2.output_assignment should equal ((x, PACombination(b))::Nil)                                                 
      // TODO: how to detect that this is not satisfiable ?
    }
    it("should merge inequations to get equations") {
      val pac1 = c+x-b >= 0
      val pac2 = c+x-b <= 0
      val solution = PASynthesis.solve("merge_inequations", pac1, pac2)
      solution._1.global_condition should equal (PATrue())
      solution._2.output_assignment should equal ((x, PACombination(b)-PACombination(c))::Nil)
    }
    it("should detect colliding equations and return false") {
      val pac1 = c+x-b >= 1
      val pac2 = c+x-b <= 0
      val solution = PASynthesis.solve("colliding_equations", pac1, pac2)
      solution._1.global_condition should equal (PAFalse())
    }
    it("should solve inequations when variables are bounded only on one side") {
      val pac1 = c+x-b >= 0
      val pac2 = (b-c)-y >= -1
      val solution = PASynthesis.solve("bounded_one_side", pac1, pac2)
      solution._1.global_condition should equal (PATrue())
      solution._2.output_assignment should equal ((y, b+1-c)::(x, b-c)::Nil)
    }
    it("should solve inequations when a variables are bounded on the right") {
      val pac1 = (b-c)-x >= 0
      val pac2 = (b+1-d)-x >= 0
      val solution = PASynthesis.solve("bounded_right", pac1, pac2)
      solution._1.global_condition should equal (PATrue())
      println(solution._2)
      solution._2.output_assignment should equal ((x, PAMinimum((b+1-d)::(b-c)::Nil))::Nil)
    }
    it("should solve a simple inequation system") {
      val pac1 = c-x >= 0
      val pac2 = x-b >= 0
      val solution = PASynthesis.solve("simple_inequation", pac1, pac2)
      println(solution._2)
      solution._1.global_condition should equal ((c-b) >= 0)
      solution._2.output_assignment should equal ((x, PACombination(c))::Nil)
    }
    it("should solve an inequation system with partial modulo ending") {
      val pac1 = (-c)-x+(y*3) === 0
      val pac2 = x*1 >= 0
      val pac3 = (-x)+2 >= 0
      val solution = PASynthesis.solve("modulo_ending", pac1, pac2, pac3)
      println(solution._1)
      println(solution._2)
      //solution._1.global_condition should equal (PAGreaterEqZero(PACombination(c)-PACombination(b))::Nil)
      //solution._2.output_assignment should equal ((x, PACombination(c))::Nil)
    }
    it("should be able to produce if-then-else construct") {
      val pac1 = x >= 0
      val pac2 = y-x >= 0
      val pac3 = z >= 0
      val pac4 = y-z >= 0
      val pac5 = ((y*3) - (z*2) + x) - b === 0
      val solution = PASynthesis.solve("find_if", pac1, pac2, pac3, pac4, pac5)
      println(solution._1)
      println(solution._2)
    }
    // FAILING !!
    /*it("should terminate on problems with big integers") {
      val pac1 = (b+(x*(-2147483648)))+y*(-2147483647) === 0
      val solution = PASynthesis.solve("terminates", pac1)
      println(solution._1)
      println(solution._2)
    }*/
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
    it("should solve problems with disjunctions") {
      val pac = (x >= 0) && ((x >= 1) || ((y+z) < 0)) && ((x < 1) || ((y-z) > 0))
      val solution = PASynthesis.solve(pac)
      solution._1.global_condition should be (PATrue())
      println(solution._1)
      println(solution._2)
    }
    it("should solve the max problem") {
      val pac = (x >= b) && (x >= c) && (x >= d)  && ((x <= b) || (x <= c) || (x <= d))
      val solution = PASynthesis.solve(pac)
      println(solution._1)
      println(solution._2)
    }
  }
}