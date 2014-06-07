package synthesis

import org.scalatest._

class PASynthesisTest extends FunSpec with Matchers {
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
      val v = PASynthesis.newOutputVariable(Nil, l_output_vars)
      l_output_vars should not contain v
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
      println(solution._2)
      solution._1 should equal (PACondition(Nil, PATrue()))
    }
    it("should solve normally constrained equations 1") {
      val pac1 = b + x*2 ===0
      val solution = PASynthesis.solve("constrained1", pac1)
      println(solution._2)
      solution._1 should equal (PACondition(Nil, PADivides(2, b)))
      solution._2.input_assignment should equal ((x0, PADivision(b, 2))::Nil)
      solution._2.output_assignment should equal ((x, -x0)::Nil)
    }
    it("should solve normally constrained equations 2") {
      val pac1 = b  + x*10 + y*14 + z*35 === 0
      val pac2 = c*2 -x*3  +        z*35 === 0
      val pac3 = -b - x*5  +        z*8  === 0
      val solution = PASynthesis.solve("constrained2", pac1, pac2, pac3)
      println(solution._2)
      solution._1.execute(Map[InputVar, Int]() + (b -> 89) + (c -> 1891)) should be (true)
      solution._1.execute(Map[InputVar, Int]() + (b -> 89) + (c -> 1892)) should be (false)
      solution._1.execute(Map[InputVar, Int]() + (b -> 90) + (c -> 1891)) should be (false)
      val vb = 89
      val vc = 1891
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb)+ (c -> vc))
      val (vx, vy, vz) = (mapping(x), mapping(y), mapping(z))
      (vb  + vx*10 + vy*14 + vz*35) should equal (0)
      (vc*2 -vx*3  +        vz*35) should equal (0)
      (-vb - vx*5  +        vz*8) should equal (0)
    }
    it("should solve overconstrained equations") {
      val x0 = InputVar("x0")
      val pac1 = b+(x*2) === 0
      val pac2 = (c*2)-(x*3) === 0
      val solution = PASynthesis.solve("overconstrained", pac1, pac2)
      println(solution._1)
      println(solution._2)
      solution._1.execute(Map[InputVar, Int]() + (b -> -2)+ (c -> 3)) should equal (false)
      solution._1.execute(Map[InputVar, Int]() + (b -> -4)+ (c -> 3)) should equal (true)
      solution._1.execute(Map[InputVar, Int]() + (b -> -3)+ (c -> 3)) should equal (false)
      solution._1.execute(Map[InputVar, Int]() + (b -> -4)+ (c -> 4)) should equal (false)
      solution._1.execute(Map[InputVar, Int]() + (b -> -2)+ (c -> 4)) should equal (false)
      solution._1.execute(Map[InputVar, Int]() + (b -> 4)+ (c -> -3)) should equal (true)
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
      solution._2.execute(Map[InputVar, Int]() + (b -> 5))(x) should equal (5)
    }
    it("should solve the advanced bezout problem") {
      val eq1 = b + x*10 + y*15 + z*6 === 2
      val solution = PASynthesis.solve("finding_bezout1", eq1)
      solution._1.global_condition should equal (PATrue())
      println(solution._2)
      val vb = 7
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb))
      val (vx, vy, vz) = (mapping(x), mapping(y), mapping(z))
      (vb + vx*10 + vy*15 + vz*6) should equal (2)
    }
    it("should solve the advanced bezout problem with precondition") {
      val eq1 = b + x*9 + y*15 + z*6 === 2
      val solution = PASynthesis.solve("finding_bezout2", eq1)
      solution._1.global_condition should equal (PADivides(3, b+(-2)))
      println(solution._2)

      val vb1 = 8
      val mapping1 = solution._2.execute(Map[InputVar, Int]() + (b -> vb1))
      val (vx1, vy1, vz1) = (mapping1(x), mapping1(y), mapping1(z))
      (vb1 + vx1*9 + vy1*15 + vz1*6) should equal (2)

      val vb2 = 7
      val mapping2 = solution._2.execute(Map[InputVar, Int]() + (b -> vb2))
      val (vx2, vy2, vz2) = (mapping2(x), mapping2(y), mapping2(z))
      (vb2 + vx2*9 + vy2*15 + vz2*6) should not equal (2)
    }
    it("should solve the advanced bezout problem with more postconditions") {
      val eq1 = b + x*10 + y*15 + z*6 === 0
      val eq2 = x > 5
      val eq3 = y < 18
      val solution = PASynthesis.solve("finding_bezout3", eq1, eq2, eq3)
      solution._1.global_condition should equal (PATrue())
      val vb = 179
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb))
      val (vx, vy, vz) = (mapping(x), mapping(y), mapping(z))
      (vb + vx*10 + vy*15 + vz*6) should equal (0)
      (vx > 0) should be (true)
      (vy < 18) should be (true)
    }
    it("should merge inequations to get equations") {
      val pac1 = c+x-b >= 0
      val pac2 = c+x-b <= 0
      val solution = PASynthesis.solve("merge_inequations", pac1, pac2)
      solution._1.global_condition should equal (PATrue())
      solution._2.output_assignment should equal ((x, PACombination(b)-PACombination(c))::Nil)
    }
    it("should detect colliding inequations and return false") {
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
      val vb = 179
      val vc = 351
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb) + (c -> vc))
      val (vx, vy) = (mapping(x), mapping(y))
      (vc + vx - vb >= 0) should be (true)
      (vb - vc - vy >= -1) should be (true)
    }
    it("should solve inequations when a variables are bounded on the right") {
      val pac1 = (b-c)-x >= 0
      val pac2 = (b+1-d)-x >= 0
      val solution = PASynthesis.solve("bounded_right", pac1, pac2)
      solution._1.global_condition should equal (PATrue())
      println(solution._2)

      val vb = 179
      val vc = 351
      val vd = 243
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb) + (c -> vc) + (d -> vd))
      val (vx) = (mapping(x))
      ((vb-vc)-vx >= 0) should be (true)
      ((vb+1-vd)-vx >= 0) should be (true)
    }
    it("should solve a simple inequation system") {
      val pac1 = c-x >= 0
      val pac2 = x-b >= 0
      val solution = PASynthesis.solve("simple_inequation", pac1, pac2)
      println(solution._2)
      solution._1.global_condition should equal ((c-b) >= 0)
      val vb = 179
      val vc = 351
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb) + (c -> vc))
      val (vx) = (mapping(x))
      (vc-vx >= 0) should be (true)
      (vx-vb >= 0) should be (true)
    }
    it("should solve an inequation system with partial modulo ending") {
      val pac1 = (-c)-x+(y*3) === 0
      val pac2 = x*1 >= 0
      val pac3 = (-x)+2 >= 0
      val solution = PASynthesis.solve("modulo_ending", pac1, pac2, pac3)
      solution._1.global_condition should equal (PATrue())
      println(solution._2)
      val vc = 351
      val mapping = solution._2.execute(Map[InputVar, Int]() + (c -> vc))
      val (vx, vy) = (mapping(x), mapping(y))
      ((-vc)-vx+(vy*3)) should equal (0)
      (vx >= 0) should be (true)
      ((-vx)+2 >= 0) should be (true)
    }
    it("should be able to produce if-then-else construct") {
      val pac1 = x >= 0
      val pac2 = y-x >= 0
      val pac3 = z >= 0
      val pac4 = y-z >= 0
      val pac5 = ((y*3) - (z*2) + x) - b === 0
      val solution = PASynthesis.solve("find_if", pac1, pac2, pac3, pac4, pac5)
      println(solution._2)
      solution._1.execute(Map[InputVar, Int]() + (b -> -3)) should be (false)

      val vb = 7
      solution._1.execute(Map[InputVar, Int]() + (b -> vb)) should be (true)
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb))

      val (vx, vy, vz) = (mapping(x), mapping(y), mapping(z))
      (vx >= 0) should be (true)
      (vy-vx >= 0) should be (true)
      (vz >= 0) should be (true)
      (vy-vz >= 0) should be (true)
      ((vy*3) - (vz*2) + vx) should equal (vb)
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
      val mapping = solution._2.execute(Map[InputVar, Int]())
      val (vx, vy, vz) = (mapping(x), mapping(y), mapping(z))
      ((vx >= 0) && ((vx >= 1) || ((vy+vz) < 0)) && ((vx < 1) || ((vy-vz) > 0))) should be (true)
    }
    it("should solve the max problem") {
      val pac = (x >= b) && (x >= c) && (x >= d)  && ((x <= b) || (x <= c) || (x <= d))
      val solution = PASynthesis.solve(pac)
      println(solution._1)
      println(solution._2)
      val vb = 7
      val vc = 15
      val vd = -9
      solution._1.execute(Map[InputVar, Int]() + (b -> vb) + (c -> vc) + (d -> vd)) should be (true)
      val mapping = solution._2.execute(Map[InputVar, Int]() + (b -> vb) + (c -> vc) + (d -> vd))
      mapping(x) should equal (15)
    }
    it("should solve the hour-minut-second problem") {
      val seconds = I("seconds")
      val s = O("s")
      val m = O("m")
      val h = O("h")
      val condition = (
           seconds === s + (m * 60) + (h*3600)
        && s >= 0 && s < 60
        && m >= 0 && m < 60
      )
      val solution = PASynthesis.solve("getHourMinutSeconds", condition)

      val vseconds = -69
      println(solution._2)
      solution._1.execute(Map[InputVar, Int]() + (seconds -> vseconds)) should be (true)
      val mapping = solution._2.execute(Map[InputVar, Int]() + (seconds -> vseconds))
      mapping(s) should equal (51)
      mapping(m) should equal (58)
      mapping(h) should equal (-1)
    }
    it("should not produce empty if-then-else") {
      val condition = x*3 >= b && x*2 <= c && x*5 >= b-c && x*7 <= b*2+c
      val solution = PASynthesis.solve("NoEmptyIfthenElse", condition)
      println(solution._1)
      println(solution._2)
    }
  }
}
