package synthesis

import org.scalatest._
import org.scalatest.matchers._

class CommonTest extends Spec with ShouldMatchers {
  describe("Auxiliary functions") {
    it("should insert zeros properly") {
      Common.insertPreviousZeros(List(-5, -6, 0, 3, 0, 2), List(17, -42, -53, 28)) should equal (List(17, -42, 0, -53, 0, 28))
    }
    it("should compute scalar product properly") {
      Common.scalarProduct(List(3, 6, -2), List(5, -6, 4)) should equal (3*5+6*(-6)+4*(-2))
    }
    it("should replaceEverythingByCoef1ExceptCoef2AtIndex properly") {
      Common.replaceEverythingByCoef1ExceptCoef2AtIndex(List((0, 1), (1, 5), (2, 4), (3, 6)), 3, 4, 2) should equal (List(3, 3, 4, 3))
    }
    it("should replaceEverythingByZeroExcept1AtIndex properly") {
      Common.replaceEverythingByZeroExcept1AtIndex(List((0, 1), (1, 5), (2, 4), (3, 6)), 2) should equal (List(0, 0, 1, 0))
    }
    it("should putCoef1AtIndex1andCoef2AtIndex2 properly") {
      Common.putCoef1AtIndex1andCoef2AtIndex2(List((0, 1), (1, 5), (2, 4), (3, 6)), 3, 1, 2, 3) should equal (List(0, 3, 0, 2))
    }
    it("should replaceElementAtIndexByCoef properly") {
      Common.replaceElementAtIndexByCoef(List((0, 1), (1, 5), (2, 4), (3, 6)), 2, 1) should equal (List(1, 5, 1, 6))
    }
  }
  
  describe("bezout function") {
    it("should solve the simple bezout identity") {
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
    it("should solve the more complex bezout identity") {
      Common.bezoutWithBase(6) should equal (Nil)
      Common.bezoutWithBase(6, 3) should equal (List(List(-2)))
      Common.bezoutWithBase(-18, 6) should equal (List(List(3)))
      Common.bezoutWithBase(-7, 3) should equal (List(List(2)))
      Common.bezoutWithBase(-8, 3) should equal (List(List(3)))
      Common.bezoutWithBase(-13, 7) should equal (List(List(2)))
      Common.bezoutWithBase(-11, 8) should equal (List(List(1)))
      Common.bezoutWithBase(-12, 8) should equal (List(List(1)))
      Common.bezoutWithBase(-13, 8) should equal (List(List(2)))
      Common.bezoutWithBase(-13, 8, 0) should equal (List(List(2, 0), List(0, 1)))
      Common.bezoutWithBase(-13, 42, 1, 17) should equal (List(List(0, 13, 0), List(1, -42, 0), List(0, -17, 1)))
      Common.bezoutWithBase(5, 6, 4, 3) match {
        case l@((a1::a2::a3::Nil)::(b1::b2::b3::Nil)::(c1::c2::c3::Nil)::Nil) =>
          println(l)
          (5+a1*6+a2*4+a3*3) should equal (0)
          (b1*6+b2*4+b3*3) should equal (0)
          (c1*6+c2*4+c3*3) should equal (0)
        case l => l should equal ("a matrix with nine elements")
      }
      Common.bezoutWithBase(17, 10, 15, 6) match {
        case l@((a1::a2::a3::Nil)::(b1::b2::b3::Nil)::(c1::c2::c3::Nil)::Nil) =>
          println(l)
          (17+a1*10+a2*15+a3*6) should equal (0)
          (b1*10+b2*15+b3*6) should equal (0)
          (c1*10+c2*15+c3*6) should equal (0)
        case l => l should equal ("a matrix with nine elements")
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