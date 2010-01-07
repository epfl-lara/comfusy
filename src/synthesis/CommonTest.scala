package synthesis

import org.scalatest._
import org.scalatest.matchers._

class CommonTest extends Spec with ShouldMatchers {
  import Common._
  
  describe("Common functions") {
    it("should compute the GCD of a list") {
      gcdlist((-18)::12::0::36::Nil) should equal (6)
    }
    it("specialMod") {
      smod(10, 7) should equal(3)
      smod(11, 7) should equal(-3)
      smod(14, 7) should equal(0)
      smod(3, 8) should equal(3)
      smod(4, 8) should equal(-4)
      smod(5, 8) should equal(-3)
      smod(-10, 7) should equal(-3)
      smod(-11, 7) should equal(3)
      smod(-14, 7) should equal(0)
      smod(-3, 8) should equal(-3)
      smod(-4, 8) should equal(-4)
      smod(-5, 8) should equal(3)
      smod(1, -1) should equal(0)
      smod(5, -3) should equal(-1)
    }
  }
  describe("Auxiliary functions") {
    it("should insert zeros properly") {
      insertPreviousZeros(List(-5, -6, 0, 3, 0, 2), List(17, -42, -53, 28)) should equal (List(17, -42, 0, -53, 0, 28))
    }
    it("should compute scalar product properly") {
      scalarProduct(List(3, 6, -2), List(5, -6, 4)) should equal (3*5+6*(-6)+4*(-2))
    }
    it("should replaceEverythingByCoef1ExceptCoef2AtIndex properly") {
      replaceEverythingByCoef1ExceptCoef2AtIndex(List((0, 1), (1, 5), (2, 4), (3, 6)), 3, 4, 2) should equal (List(3, 3, 4, 3))
    }
    it("should replaceEverythingByZeroExcept1AtIndex properly") {
      replaceEverythingByZeroExcept1AtIndex(List((0, 1), (1, 5), (2, 4), (3, 6)), 2) should equal (List(0, 0, 1, 0))
    }
    it("should putCoef1AtIndex1andCoef2AtIndex2 properly") {
      putCoef1AtIndex1andCoef2AtIndex2(List((0, 1), (1, 5), (2, 4), (3, 6)), 3, 1, 2, 3) should equal (List(0, 3, 0, 2))
    }
    it("should replaceElementAtIndexByCoef properly") {
      replaceElementAtIndexByCoef(List((0, 1), (1, 5), (2, 4), (3, 6)), 2, 1) should equal (List(1, 5, 1, 6))
    }
  }
  
  describe("bezout function") {
    it("should solve the simple bezout identity") {
      computing_mode = OTBezout() 
      bezout(6) should equal (Nil)
      bezout(6, 3) should equal (List(-2))
      bezout(-18, 6) should equal (List(3))
      bezout(-7, 3) should equal (List(2))
      bezout(-8, 3) should equal (List(3))
      bezout(-13, 7) should equal (List(2))
      bezout(-11, 8) should equal (List(1))
      bezout(-12, 8) should equal (List(1))
      bezout(-13, 8) should equal (List(2))
      bezout(-13, 42, 1, 17) should equal (List(0, 13, 0))
      bezout(1, -3, 2) should equal (List(1, 1))
      bezout(1, -3, -2) should equal (List(1, -1))
      bezout(6, 5, 3) match {
        case x::y::Nil => (6+x*5+y*3) should equal (0)
        case l => l should equal ("a list with two elements")
      }
      bezout(17, 10, 15, 6) match {
        case x::y::z::Nil => (17+x*10+y*15+z*6) should equal (0)
        case l => l should equal ("a list with three elements")
      }
      bezout(6, 12, 27, 51) match {
        case x::y::z::Nil => (6+x*12+y*27+z*51) should equal (0)
        case l => l should equal ("a list with three elements")
      }
      bezout(7, 12, 28, 51) match {
        case x::y::z::Nil => (7+x*12+y*28+z*51) should equal (0)
        case l => l should equal ("a list with three elements")
      }
      bezout(1973, 2*3*5,2*3*7,2*5*7,3*5*7) match {
        case x::y::z::w::Nil => (1973+x*2*3*5+y*2*3*7+z*2*5*7+w*3*5*7) should equal (0)
        case l => l should equal ("a list with four elements")
      }
    }
    it("should solve the more complex bezout identity") {
      computing_mode = OTBezout() 
      bezoutWithBase(6) should equal (Nil)
      bezoutWithBase(6, 3) should equal (List(List(-2)))
      bezoutWithBase(-18, 6) should equal (List(List(3)))
      bezoutWithBase(-7, 3) should equal (List(List(2)))
      bezoutWithBase(-8, 3) should equal (List(List(3)))
      bezoutWithBase(-13, 7) should equal (List(List(2)))
      bezoutWithBase(-11, 8) should equal (List(List(1)))
      bezoutWithBase(-12, 8) should equal (List(List(1)))
      bezoutWithBase(-13, 8) should equal (List(List(2)))
      bezoutWithBase(-13, 8, 0) should equal (List(List(2, 0), List(0, 1)))
      bezoutWithBase(-13, 42, 1, 17) should equal (List(List(0, 13, 0), List(1, -42, 0), List(0, -17, 1)))
      bezoutWithBase(1, -1) should equal (List(List(1)))
      bezoutWithBase(1, -3, 2) match {
        case l@((a1::a2::Nil)::(b1::b2::Nil)::Nil) =>
          println(l)
          (1-a1*3+a2*2) should equal (0)
          (-b1*3+b2*2) should equal (0)
          (a1*b2-a2*b1) should not equal (0)
        case l => l should equal ("a matrix with four elements")
      }
      bezoutWithBase(1, -3, -2) match {
        case l@((a1::a2::Nil)::(b1::b2::Nil)::Nil) =>
          println(l)
          (1-a1*3-a2*2) should equal (0)
          (-b1*3-b2*2) should equal (0)
          (a1*b2-a2*b1) should not equal (0)
        case l => l should equal ("a matrix with four elements")
      }
      bezoutWithBase(1, -23, -13) match {
        case l@((a1::a2::Nil)::(b1::b2::Nil)::Nil) =>
          println(l)
          (1-a1*23-a2*13) should equal (0)
          (-b1*23-b2*13) should equal (0)
          (a1*b2-a2*b1) should not equal (0)
        case l => l should equal ("a matrix with four elements")
      }
      bezoutWithBase(5, 6, 4, 3) match {
        case l@((a1::a2::a3::Nil)::(b1::b2::b3::Nil)::(c1::c2::c3::Nil)::Nil) =>
          println(l)
          (5+a1*6+a2*4+a3*3) should equal (0)
          (b1*6+b2*4+b3*3) should equal (0)
          (c1*6+c2*4+c3*3) should equal (0)
          (a1*b2*c3+a2*b3*c1+a3*b1*c2-a1*b3*c2-a2*b1*c3-a3*b2*c1) should not equal (0)
        case l => l should equal ("a matrix with nine elements")
      }
      bezoutWithBase(17, 10, 15, 6) match {
        case l@((a1::a2::a3::Nil)::(b1::b2::b3::Nil)::(c1::c2::c3::Nil)::Nil) =>
          println(l)
          (17+a1*10+a2*15+a3*6) should equal (0)
          (b1*10+b2*15+b3*6) should equal (0)
          (c1*10+c2*15+c3*6) should equal (0)
          (a1*b2*c3+a2*b3*c1+a3*b1*c2-a1*b3*c2-a2*b1*c3-a3*b2*c1) should not equal (0)
        case l => l should equal ("a matrix with nine elements")
      }
    }
  }
  describe("new bezout functions") {
    computing_mode = MMBezout() 
    it("should solve the advanced euclid algorithm") {
      {val (u, v, k) = advancedEuclid(19*13, 19*17)
      k should equal (19)
      (k+u*19*13+v*19*17) should equal (0)}
      {val (u, v, k) = advancedEuclid(-19*13, 19*17)
      k should equal (19)
      (k-u*19*13+v*19*17) should equal (0)}
      {val (u, v, k) = advancedEuclid(19*13, -19*17)
      k should equal (19)
      (k+u*19*13-v*19*17) should equal (0)}
      {val (u, v, k) = advancedEuclid(-19*13, -19*17)
      k should equal (19)
      (k-u*19*13-v*19*17) should equal (0)}
      {val (u, v, k) = advancedEuclid(0, -19*17)
      k should equal (19*17)
      (k-v*19*17) should equal (0)}
      {val (u, v, k) = advancedEuclid(-19*17, 0)
      k should equal (19*17)
      (k-u*19*17) should equal (0)}
    }
    it("should find witnesses") {
      {val List(u) = bezoutMM(List(-19*13))
      (19*13-u*19*13) should equal (0)}
      {val List(u) = bezoutMM(List(19*13))
      (19*13+u*19*13) should equal (0)}
      {val List(u, v) = bezoutMM(List(-19*13, 19*17))
      (19-u*19*13+v*19*17) should equal (0)}
      {val List(u, v, w) = bezoutMM(List(19*13, -19*17, 13*17))
      (1+u*19*13-v*19*17+w*13*17) should equal (0)}
    }
    it("should find bases when there are only two elements") {
      { val input = List(5, 7)
        val List(_, List(u, v)) = bezoutWithBaseMM(0, input)
        5*u+7*v should equal (0)
        (u-v) should not equal (0) }
      { val input = List(-5, 7)
        val List(_, List(u, v)) = bezoutWithBase(0, input)
        -5*u+7*v should equal (0)
        (u-v) should not equal (0) }
      { val input = List(-5, -7)
        val List(_, List(u, v)) = bezoutWithBase(0, input)
        -5*u-7*v should equal (0)
        (u-v) should not equal (0) }
      { val input = List(5, -7)
        val List(_, List(u, v)) = bezoutWithBase(0, input)
        5*u-7*v should equal (0)
        (u-v) should not equal (0) }
    }
    it("should find bases when there are three elements") {
      { val input = List(10, 15, 6)
        val List(_, List(u1, v1, w1), List(u2, v2, w2)) = bezoutWithBaseMM(0, input)
        10*u1+15*v1+6*w1 should equal (0)
        10*u2+15*v2+6*w2 should equal (0)
        ((u1*v2-u2*v1 != 0) || (w1*v2-w2*v1 != 0) || (u1*w2-u2*w1 != 0)) should be (true) 
      }
      { val input = List(19*13, -19*17, 13*17)
        val List(_, List(u1, v1, w1), List(u2, v2, w2)) = bezoutWithBase(0, input)
        19*13*u1-19*17*v1+13*17*w1 should equal (0)
        19*13*u2-19*17*v2+13*17*w2 should equal (0)
        ((u1*v2-u2*v1 != 0) || (w1*v2-w2*v1 != 0) || (u1*w2-u2*w1 != 0)) should be (true) 
      }
    }
    it("should find bases even if one element is null") {
      { val input = List(10, 0, 6)
        val List(_, List(u1, v1, w1), List(u2, v2, w2)) = bezoutWithBase(0, input)
        10*u1+0*v1+6*w1 should equal (0)
        10*u2+0*v2+6*w2 should equal (0)
        ((u1*v2-u2*v1 != 0) || (w1*v2-w2*v1 != 0) || (u1*w2-u2*w1 != 0)) should be (true)
        (Math.abs(v1) == 1 || Math.abs(v2) == 1) should be (true)
      }
    }
    it("should find bases when there are four elements") {
      /*{ val input = List(2*3*5, 2*3*11, 3*5*7, 2*5*7)
        val List(List(u1, v1, w1, z1), List(u2, v2, w2, z2), List(u3, v3, w3, z3)) = bezoutWithBase(input)
        10*u1+15*v1+6*w1 should equal (0)
        10*u2+15*v2+6*w2 should equal (0)
        ((u1*v2-u2*v1 != 0) || (w1*v2-w2*v1 != 0) || (u1*w2-u2*w1 != 0)) should be (true) 
      }*/
    }
  }
}