package decision

;

//import Z3Converter._
//import Reconstruction._
//import Phase3._
import AST._
import Flags._
import Repl.{solveAndPrint, mkRepl}

import java.io.{InputStreamReader => ISR, StringReader => SR}


object CountOrderings {
  def run(form: Formula) = {
    println("Formula:")
    NormalForms.nnf(form).print
    println

    countOnly = true
    withMinMax = false
    intermediateZ3 = false
    countNaive = false
    naiveCounts = Nil
    println("  # conjunctions       : " + NormalForms(form).size)

    countNaive = true
    solveAndPrint(form)
    println("  Naive Bell numbers  : " + naiveCounts)
    countNaive = false

    println("Transitive Closure")
    solveAndPrint(form)

    withMinMax = true
    println("Min / max")
    solveAndPrint(form)
    withMinMax = false

    intermediateZ3 = true
    println("Z3 at nodes")
    solveAndPrint(form)
    intermediateZ3 = false

    withMinMax = true
    intermediateZ3 = true
    println("Min/max WITH  Z3 at nodes ")
    solveAndPrint(form)
    withMinMax = false
    intermediateZ3 = false

  }

  // Use this to get the old behavour
  // def main(args : Array[String]) = preDefForm

  // The parser
  def main(args: Array[String]) = {
    mkRepl(run)
  }

}
