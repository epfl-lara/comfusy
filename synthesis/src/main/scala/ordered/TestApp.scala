package synthesis.ordered

import synthesis.ordered._
import synthesis.ordered.AST._
import synthesis.ordered.Primitives._
import synthesis.ordered.GuessOrdering._

import synthesis.{PASynthesis => PA}

object TestApp {
  val A = Symbol("A")
  val B = Symbol("B")
  val C = Symbol("C")
  val a = Symbol("a")
  val b = Symbol("b")
  val c = Symbol("c")
/*
  def main(args: Array[String]): Unit = {

    val A1 = (A ++ C) seq B
    val A2 = (A ** C) seq emptyset
    val A3 = (a + b) === c
    val A4 = B.card > c
    val formula_ = (A1 && A2) && A3 && A4 && (c > 0)
    val formula = (A slt B) //&& (B slt C)
    val dnfStream = NormalForms(formula)

    //    formula.print
    for (conj <- dnfStream) {
      println("**********************************")
      conj.print
      println
      //      println("ints: " + intvars(conj) + ", sets: " + setvars(conj))
      //      test(List(A), List(B,C), List(a), List(b,c), conj)
      GuessOrdering.guess(conj.formulas)
    }
  }
*/
  def test2(f: Formula) = {
    println(setvars(f).toList.map {_.name}.size + ", " + setvars(f).toList.map {_.name})
    //    test(List(A), List(B,C), List(a), List(b,c), f)
    //val svars = setvars(f).toList.map{_.name}
    //test(List(A,B), svars remove{List(A,B).contains}, Nil, Nil, f)
    println("--------------");
    f.print;
    println("--------------")
    val f0 = QFBAPAtoPATranslator(f)
    f0.print
    println
    println("-----------------------------------------------------------------------------------")
    val f1 = QFBAPAtoPATranslator.rewriteITEExpression(f0)
    println("Without ITE:")
    f1.print
    println
    println("-----------------------------------------------------------------------------------")
    val f2 = QFBAPAtoPATranslator.ordFormToArithForm(NormalForms.nnf(f1))
    println("PASynth Formula:")
    println(f2)
    println
    println("-----------------------------------------------------------------------------------")
    println
    val _ = QFBAPAtoPATranslator.callSynth(NormalForms.nnf(f1))
    println("PASynth Code: Done")
    println
    println("-----------------------------------------------------------------------------------")
    println
    //System.exit(0) // abort after one guess
    true
  }


  def test(k: List[Symbol], l: List[Symbol], x: List[Symbol], y: List[Symbol], f: Formula): Boolean = {
    try {
      val (preCard, mSt, paPc, paPg, setAs) = BapaConverter.solve(k, l, x, y, f)
      val PA.PACondition(xx, global) = paPc
      val isFalse = (global match {case PA.PAFalse() => true; case _ => false})
      if (!isFalse) {
        println("After Conversion:")
        println("PreCard = " + preCard)
        println("Formula=" + mSt)
        println("Precond=" + paPc)
        println("Code=" + paPg)
        println("Set Assignments=" + setAs)
        //        println
        true
      } else false
    } catch {
      case e => println(e); false //e.printStackTrace(); false
    }
  }
}
