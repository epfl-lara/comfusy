package synthesis.bapa

import synthesis.bapa.Printer._

import ASTBAPASyn._

object Examples {

//---------------

    val l21 = List("B1", "B2")
    val l22 = List("A")
    val l23: List[String] = Nil
    val l24: List[String] = Nil
    val a21 = IntLessEqual(IntConst(2), Card(SetVar("A")))
    val f21 = And(FAtom(SetSubset(SetVar("A"), SetVar("B1"))), And(FAtom(SetSubset(SetVar("A"), SetVar("B2"))), FAtom(a21)))
    val t2 = Task(l21, l22, l23, l24, f21)

//---------------

    val l11 = List("A", "B")
    val l12 = List("S")
    val l13: List[String] = Nil
    val l14: List[String] = Nil
    val f11 = And(FAtom(SetSubset(SetVar("A"), SetVar("S"))), FAtom(IntLessEqual(Card(SetVar("S")), Card(SetVar("B")))))
    val t1 = Task(l11, l12, l13, l14, f11)

//---------------

    def run (name: String, t: Task): Unit = t match {
      case Task(x, y, k, l, f) => {
        print_Task(t)
        val f1 = synthesis.bapa.Algorithm.step1(f)
        print_BAPAFormula(f1)
        println(" ")
        val (f2, mAll, vars) = synthesis.bapa.Algorithm.step2and3(f1, x ::: y)
        print_BAPAFormula(f2)
        println(" ")
        val f3 = synthesis.bapa.Algorithm.step4(mAll, x)
        print_BAPAFormula(f3)
        println(" ")
        synthesis.bapa.Algorithm.step5(x, y, k, l, vars, f2, f3, mAll)
     }
     println("finished!")
   }

// -----

  def runExamples() {
    run("t1", t1)
    run("t2", t2)
  }


}
