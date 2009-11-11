package synthesis

import org.scalatest._
import org.scalatest.matchers._

class CommonTest extends Spec with ShouldMatchers {
  describe("bezout function") {
    it("should compute the simple bezout identity") {
      Common.bezout(6) should equal (Nil)
      Common.bezout(6, 3) should equal (List(-2))
      Common.bezout(-18, 6) should equal (List(3))
      Common.bezout(-7, 3) should equal (List(2))
      Common.bezout(-8, 3) should equal (List(3))
      Common.bezout(-13, 7) should equal (List(2))
      Common.bezout(-11, 8) should equal (List(1))
      Common.bezout(-12, 8) should equal (List(1))
      Common.bezout(-13, 8) should equal (List(2))
      Common.bezout(-13, 42, 1, 17) should equal (List(0, 13, 0))
      Common.bezout(6, 5, 3) match {
        case x::y::Nil => (6+x*5+y*3) should equal (0)
        case l => l should equal ("a list with two elements")
      }
      Common.bezout(17, 10, 15, 6) match {
        case x::y::z::Nil => (17+x*10+y*15+z*6) should equal (0)
        case l => l should equal ("a list with three elements")
      }
      Common.bezout(6, 12, 27, 51) match {
        case x::y::z::Nil => (6+x*12+y*27+z*51) should equal (0)
        case l => l should equal ("a list with three elements")
      }
      Common.bezout(7, 12, 28, 51) match {
        case x::y::z::Nil => (7+x*12+y*28+z*51) should equal (0)
        case l => l should equal ("a list with three elements")
      }
      Common.bezout(1973, 2*3*5,2*3*7,2*5*7,3*5*7) match {
        case x::y::z::w::Nil => (1973+x*2*3*5+y*2*3*7+z*2*5*7+w*3*5*7) should equal (0)
        case l => l should equal ("a list with four elements")
      }
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
}