package decision

import z3._
import java.io.{InputStreamReader => ISR, StringReader => SR}
/*
object SimpleTest {
  import AST._
  import Primitives._

  val A = Symbol("A")
  val B = Symbol("B")
  val C = Symbol("C")

  val N = Symbol("num")
  val F = Symbol("f")
  val Servers = Symbol("Servers")
  val Byz = Symbol("Byz")
  val Corr = Symbol("Corr")
  val S = Symbol("S")
  val srv = Symbol("srv")

  def preDefForm = {
    //val form = (A slt B) && (A subseteq C) && (B subseteq C)
    // val form = (C.inf === 1) && (C.sup === 10) && (C seq A ++ B) && (A slt B) && (A.card === 5) && (B.card === 5)
    //val form = (5 selem A) && (3 selem A) // && (A.inf < B.inf) && (B.inf < A.sup) && (F === B.inf)

    // val form = (1 selem A) && (A subseteq B)
    // val form = (A slt B) && (A subseteq C) && (B subseteq C)

    // val form = (A.inf < B.inf) && (B.inf < A.sup) && (A.sup < B.sup) && (1 <= A.inf) && (B.sup <= 10) && (A.card === 5) && (B.card === 5) && ((A ** B).card === 0) && (N selem A)
    // val form = N selem A

    // val form = (A.inf === 0) && (A.sup === 1) && (N selem A)
    / *val form = !((
      N > 3 &&
      F > 0 &&
      N > F * 3 &&
      Servers.card === N &&
      (Byz subseteq Servers) &&
      Byz.card === F &&
      (Corr seq Servers -- Byz) &&
      (S subseteq  Servers) &&
      S.card > F
    ) implies (
      //(srv selem Corr) && (srv selem S)
      (Corr ** S).card > 0
    ))* /
    val form = ((A -- B) seq Lit(EmptySetLit)) && (A.card === 2) && (A.inf === 1) && (A.sup === 10)
    solveAndPrint(form)
  }


  def solveAndPrint(form: Formula) = {
    println("Formula:")
    NormalForms.nnf(form).print
    println

    val outSetVars = ASTUtil.setvars(form)
    val outIntVars = ASTUtil.intvars(form)

    var allModels: Set[ReconstructedValues] = Set()
    def callZ3(z3: MyZ3Context, paForm: Formula, eq: List[EquiClass], isOrderingComplete: Boolean): Phase2.Hint = {
      z3.getModel match {
        case s@Sat(t, bools, ints) => {
          println("Formula satisfiable")
          if(isOrderingComplete) allModels += Reconstruction.getReconstruction(s, outSetVars.toList, outIntVars.toList, eq)
          t()
          true
        }
        case Unsat => println("Formula unsatisfiable"); false
        case Z3Failure(e) => error("Z3 not executed.  " + e);
      }
    }
    

    for (conj <- NormalForms(form)) {
      println("Conjunction:")
      conj.print
      try {
        Phase2(Phase3.segment(callZ3))(conj)
       // Phase2(Phase2.OrderingCounter)(conj)
      } catch {
        case Phase2.UnsatException(_) =>
      }
    }

    println()
    if (!allModels.isEmpty) println("Models after reconstruction:")
    for (ReconstructedValues(intMap, setMap) <- allModels) {
      intMap.foreach(x => println("  " + x._1.toString + " -> " + x._2))
      setMap.foreach(x => println("  " + x._1.toString + " -> " + x._2.toList.sort {_ < _}.mkString("Set { ", ", ", " }")))
      println
    }
  }

  // Use this to get the old behavour
  // def main(args : Array[String]) = preDefForm

  // The parser
  / *
  def main(args: Array[String]) = {
    repl
  }
  * /

  // read-eval-print loop
  def repl {
    var input = ""
    var line = ""
    print(">> ")
    do {
      line = readLine
      if (line startsWith ":q") return
      input = input + line
    } while (!line.isEmpty)

    try {
      val form = FormulaParser.getFromStream(StreamReader(new SR(input)))
      Phase3.orderCount = 0
      solveAndPrint(form)
    } catch {
      case e: Exception =>
        e.printStackTrace
      //println(e)
    }
    println
    repl
  }
}
*/