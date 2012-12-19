package decision

import Z3Converter._
import Reconstruction._
import Phase3._
import scala.util.parsing.input._
import AST._
import Phase2.{Hint, Order}

import java.io.{InputStreamReader => ISR, StringReader => SR}

object Repl {
  var allModels: Set[ReconstructedValues] = Set()
  var outSetVars: Set[Symbol] = null
  var outIntVars: Set[Symbol] = null

  def callZ3(z3: MyZ3Context, paForm: Formula, eq: List[EquiClass]): Phase2.Hint = {

    z3.push
    z3.impose(paForm)

    /*
    println
    println("Full pa formula")
    z3.printStack
    */

    val result = z3.getModel match {
      case s@Sat(deleteModel, bools, ints) => {
        println("Formula satisfiable")
        allModels += Reconstruction.getReconstruction(s, outSetVars.toList, outIntVars.toList, eq)
        deleteModel()
        true
      }
      case Unsat => println("Formula unsatisfiable"); false
      case Z3Failure(e) => error("Z3 not executed.  " + e);
    }
    z3.pop
    result
  }

  def solveAndPrint(form: Formula) = {
    Phase3.orderCount = 0
    allModels = Set()
    //println("Formula:")
    //NormalForms.nnf(form).print

    outSetVars = ASTUtil.setvars(form)
    outIntVars = ASTUtil.intvars(form)

    val counter = new OrderingCounter

    val start = System.nanoTime
    for (conj <- NormalForms(form)) {
      //println("Conjunction:")
      //conj.print
      try {
        if (decision.Flags.countOnly)
          Phase2(counter)(conj)
        else
          Phase2(Phase3.segment(callZ3))(conj)
      } catch {
        case Phase2.UnsatException(msg) =>
          println("  " + msg)
      }
    }
    val end = System.nanoTime
    val total = ((end - start) / 1000000) / 1000.0


    if (decision.Flags.countOnly) {
      //      if (counter.partial > 0) println("  # partial orderings   : " + counter.partial)
      if (!decision.Flags.countNaive) println("  # complete orderings : " + counter.complete)
      //     if (counter.partial > 0) println("  z3 execution time[ms] : " + counter.z3time)
    }

    if (!allModels.isEmpty) println("Models after reconstruction:")

    // val sortedModels = allModels.toList.sort{_._1 < _._1}
    for (ReconstructedValues(intMap, setMap) <- allModels) {

      intMap.toList.sort {_._1.name < _._1.name}.foreach(x => println("  " + x._1.toString + " -> " + x._2))
      setMap.toList.sort {_._1.name < _._1.name}.foreach(x => println("  " + x._1.toString + " -> " + x._2.toList.sort {_ < _}.mkString("Set { ", ", ", " }")))
      println
    }

    println("Total time : " + total)
  }

  // Use this to get the old behavour
  // def main(args : Array[String]) = preDefForm

  // The parser
  /* def main(args: Array[String]) = {
    repl
  }*/


  case class Command(name: String, action: () => Unit)

  val cmdList = List(
    Command(":pruneon", () => {decision.Flags.intermediateZ3 = true}),
    Command(":pruneoff", () => {decision.Flags.intermediateZ3 = false}),
    Command(":prune", () => {
      if (decision.Flags.intermediateZ3)
        println("With intermediate calls to Z3")
      else
        println("No intermediate calls to Z3")
    }),
    Command(":libon", () => {decision.Flags.useZ3Lib = true}),
    Command(":liboff", () => {decision.Flags.useZ3Lib = false}),
    Command(":lib", () => {
      if (decision.Flags.useZ3Lib)
        println("Using native Z3 interface")
      else
        println("Using text-based Z3 interface")
    }),
    Command(":mmon", () => {decision.Flags.withMinMax = true}),
    Command(":mmoff", () => {decision.Flags.withMinMax = false}),
    Command(":mm", () => {
      if (decision.Flags.withMinMax)
        println("Add constraints from sets")
      else
        println("No constraints from sets")
    }),
    Command(":counton", () => {decision.Flags.countOnly = true}),
    Command(":countnaive", () => {decision.Flags.countNaive = true; decision.Flags.countOnly = true}),
    Command(":countoff", () => {decision.Flags.countNaive = false; decision.Flags.countOnly = false}),
    Command(":count", () => {
      if (decision.Flags.countNaive)
        println("Count naive")
      else if (decision.Flags.countOnly)
        println("Count on")
      else
        println("Count off")
    })
    )

  // read-eval-print loop
  def mkRepl(fun: Formula => Unit) {
    def repl {
      var input = ""
      var line = ""
      print(">> ")
      do {
        line = readLine
        if (line startsWith ":q") return

        if (line startsWith ":") {
          for (Command(cmd, action) <- cmdList; if line startsWith cmd) action()
          print(">> ")
          input = ""
        } else {
          input = input + line
        }
      } while (!line.isEmpty)

      if (!input.trim.isEmpty) {
        try {
          val form = FormulaParser.getFromStream(StreamReader(new SR(input)))
          fun(form)
        } catch {
          case e: Exception =>
            e.printStackTrace
          //println(e)
        }
        println
      }
      repl
    }
    repl
  }

  def main(args: Array[String]) = {
    mkRepl(solveAndPrint)
  }
}


class OrderingCounter extends ((MyZ3Context, Formula, Order) => Hint) {
  var complete = 0
  //  var partial = 0
  //  var unSat = 0
  //  var z3time = 0L

  def apply(z3: MyZ3Context, form: Formula, order: Order): Hint = {
    complete += 1
    true
  }
}
