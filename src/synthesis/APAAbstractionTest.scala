package synthesis

import org.scalatest._
import org.scalatest.matchers._

class APAAbstractionTest extends Spec with ShouldMatchers {
  def O(name: String) = OutputVar(name)
  def I(name: String) = InputVar(name)
  implicit def OutputVarToPACombination(o: OutputVar):APACombination = APACombination(o)
  implicit def InputVarToPACombination(i: InputVar):APAInputCombination = APAInputCombination(i)
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
  
  describe("Sign Abstraction") {
    it("should help to simplify expressions") {
      val bP   = (b.assumePositiveZero() - c.assumeSign(-1)) // > 0
      val bP2  = (b.assumePositiveZero() + c.assumeSign(1))  // > 0
      val bN   = (b.assumeNegativeZero() - c.assumeSign(1))  // < 0
      val bN2  = (b.assumeNegativeZero() + c.assumeSign(-1))  // < 0
      val bPZ  = (b.assumePositiveZero() - c.assumeNegativeZero()) // >= 0
      val bPZ2 = (b.assumePositiveZero() + c.assumePositiveZero()) // >= 0
      val bNZ  = (b.assumeNegativeZero() - c.assumePositiveZero()) // <= 0
      val bNZ2 = (b.assumeNegativeZero() + c.assumeNegativeZero()) // <= 0
      val bPN  = (InputVarToPACombination(c.assumeSign(1)) * b.assumeNotZero()) // != 0
      val bZ   = (b.assumeSign(0) - c.assumeSign(0)) // == 0
      val bFalse1 = (b.assumeNotZero().propagateSign(0).toInputTerm())
      val bFalse2 = (b.assumeSign(1).propagateSign(0).toInputTerm())
      val bFalse3 = (b.assumeSign(0).propagateSign(-1).toInputTerm())
      val bFalse4 = (b.assumeSign(1).propagateSign(-1).toInputTerm())
      
      (bP::bP2::Nil) foreach { case k:APAInputTerm => 
        (k > 0) should equal (APATrue())
        (k >= 0) should equal (APATrue())
        (k === 0) should equal (APAFalse())
        (k <= 0) should equal (APAFalse())
        (k < 0) should equal (APAFalse())
      }
      List(bN, bN2) foreach { case k:APAInputTerm => 
        (k > 0) should equal (APAFalse())
        (k >= 0) should equal (APAFalse())
        (k === 0) should equal (APAFalse())
        (k <= 0) should equal (APATrue())
        (k < 0) should equal (APATrue())
      }
      List(bPZ, bPZ2) foreach { case k:APAInputTerm => 
        (k >= 0) should equal (APATrue())
        (k < 0) should equal (APAFalse())
      }
      List(bNZ, bNZ2) foreach { case k:APAInputTerm => 
        (k <= 0) should equal (APATrue())
        (k > 0) should equal (APAFalse())
      }
      List(bPN) foreach { case k:APAInputTerm => 
        (k === 0) should equal (APAFalse())
      }
      List(bZ) foreach { case k:APAInputTerm => 
        (k > 0) should equal (APAFalse())
        (k >= 0) should equal (APATrue())
        (k === 0) should equal (APATrue())
        (k <= 0) should equal (APATrue())
        (k < 0) should equal (APAFalse())
      }
      List(bFalse1, bFalse2, bFalse3, bFalse4) foreach { case k:APAInputTerm => 
        (k > 0) should equal (APAFalse())
        val eq = (k >= 0)
        eq should equal (APAFalse())
        (k === 0) should equal (APAFalse())
        (k <= 0) should equal (APAFalse())
        (k < 0) should equal (APAFalse())
      }
    }
    it("should propagate internally the simplifications on mono-additions") {
      val u1 = (-b).assumePositive()
      u1 match {
        case APAInputCombination(0, (-1, b)::Nil) => b should be ('Negative)
        case _ => u1 should be (APAInputCombination(0, (-1, b)::Nil))
      }
      val u2 = (-b).assumeNegative()
      u2 match {
        case APAInputCombination(0, (-1, b)::Nil) => b should be ('Positive)
        case _ => u1 should be (APAInputCombination(0, (-1, b)::Nil))
      }
    }
    it("should propagate internally the simplifications on multiplications") {
      val u1 = (b*c).assumeNotZero()
      val u2 = (b*c).assumePositive()
      val u3 = (b*c).assumeNegative()
      List(u1, u2, u3) foreach { u => 
        u match {
          case APAInputMultiplication(List(b, c)) =>
            b should be ('NotZero)
            c should be ('NotZero)
          case _ => u should be ("an APAInputMultiplication")
        }
      }
    }
    it("should propagate internally the simplifications on multi-additions") {
      val e = b.assumePositiveZero() + (c - d)*2
      val ep1 = e.assumeSignInputTerm((c-d)*3, SignAbstraction.number(1))
      val ep2 = e.assumeSignInputTerm((c-d)*(-3), SignAbstraction.number(-1))
      val ep3 = e.assumeSignInputTerm((c-d)*(3), SignAbstraction.number(-1))
      ep1 should be ('Positive)
      ep2 should be ('Positive)
      ep3 should not be ('Positive)
    }
    it("should transform zero assumptions to zeros") {
      val e1 = APAInputMultiplication(b, c).assumeZero().simplified
      val e2 = APAInputDivision(b, c.assumePositive()).assumeZero().simplified
      val e3 = (b - c).assumeZero().simplified
      e1 should be (APAInputCombination(0))
      e2 should be (APAInputCombination(0))
      e3 should be (APAInputCombination(0))
    }
  }
}
