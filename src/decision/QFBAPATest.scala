package decision

import AST._
import collection.mutable.ListBuffer
import Z3Converter._

object QFBAPATest {
  val X = Symbol("X")
  val A = Symbol("A")
  val B = Symbol("B")
  val C = Symbol("C")
  val C1 = Symbol("C1")
  val X1 = Symbol("X1")
  val X2 = Symbol("X2")
  val X3 = Symbol("X3")
  val A0 = Symbol("A0")
  val A1 = Symbol("A1")
  val A2 = Symbol("A2")
  val This = Symbol("This")
  val NULL = Symbol("Null")
  val L1 = Symbol("L1")
  val Content = Symbol("Content")
  val Alloc = Symbol("Alloc")
  val size = Symbol("size")
  val size1 = Symbol("size1")
  val A74 = Symbol("A74")
  val A60 = Symbol("A60")
  val A45 = Symbol("A45")
  val A30 = Symbol("A30")
  val A16 = Symbol("A16")

  val p = size === 0
  val q = Content seq emptyset
  val form1 = (Content.card === size) implies ((p implies q) && (q implies p))

  val form2 = ((X.card === 1) && !(X subseteq Content) && (size === Content.card)) implies ((Content ++ X).card === size + 1)
  val form2a = ((X.card === 1) && !(X subseteq Content) && (size === Content.card) && (Content subseteq Alloc) && (X subseteq Alloc)) implies ((Content ++ X).card === size + 1)
  val form2b = ((X.card === 1) && (size === Content.card) && (Content subseteq Alloc) && (X subseteq Alloc)) implies ((Content ++ X).card === size + 1)

  val form3 = ((X.card === 1) && (size === Content.card) && (size1 === (X ++ Content).card)) implies (size1 <= size + 1)
  val form3a = ((Content subseteq Alloc) && (A subseteq Alloc) && (A.card === 1) && (B subseteq Alloc) && (B.card === 1) && (X.card === 1) && (size === Content.card) && (size1 === (X ++ Content).card)) implies (size1 <= size + 1)
  val form3b = ((Content subseteq Alloc) && (A subseteq Alloc) && (A.card === 1) && (B subseteq Alloc) && (B.card === 1) && (X.card === 1) && (size === Content.card) && (size1 === (X ++ Content).card)) implies (size1 === size + 1)

  val form4 = ((Content subseteq Alloc) && (X1.card === 1) && (X2.card === 1) && (X3.card === 1) && !(X1 subseteq Alloc) && !(X2 subseteq (Alloc ++ X1)) && !(X3 subseteq (Alloc ++ X1 ++ X2))) implies ((Content ++ X1 ++ X2 ++ X3).card === Content.card + 3)
  val form4b = ((Content subseteq Alloc) && (X1.card === 1) && (X2.card === 1) && (X3.card === 1) && !(X1 subseteq Alloc) && !(X2 subseteq Alloc) && !(X3 subseteq (Alloc ++ X1 ++ X2))) implies ((Content ++ X1 ++ X2 ++ X3).card === Content.card + 3)

  val form5 = ((Content subseteq A0) && (X1.card === 1) && !(X1 subseteq A0) && (X2.card === 1) && !(X2 subseteq A1) && (X3.card === 1) && !(X3 subseteq A2) && (A0 ++ X1 seq A1) && (A1 ++ X2 seq A2)) implies ((Content ++ X1 ++ X2 ++ X3).card === Content.card + 3)
  val form5b = ((Content subseteq A0) && (X1.card === 1) && (X2.card === 1) && !(X2 subseteq A1) && (X3.card === 1) && !(X3 subseteq A2) && (A0 ++ X1 seq A1) && (A1 ++ X2 seq A2)) implies ((Content ++ X1 ++ X2 ++ X3).card === Content.card + 3)

  val form6 = ((X.card === 1) && (X subseteq C) && (C1 seq C -- X) && ((A1 -- A0).card <= 1) && ((A2 -- A1).card <= C1.card)) implies ((A2 -- A0).card <= C.card)
  //val form6a = (L1.card === 1) & (This.card === 1) && (NULL.card === 1) && !(L1 seq NULL) && !(L1 seq This) && !(This seq NULL) &&

  def goodVC4(n: Int) = {
    val forms = new ListBuffer[Formula]()
    val elems = new ListBuffer[Term]()
    for (i <- 1 to n) {
      val Xi: Term = Symbol("X" + i)
      forms += (Xi.card === 1)
      forms += !(Xi subseteq (Alloc ++ elems))
      elems += Xi
    }
    ((Content subseteq Alloc) && forms) implies ((Content ++ elems).card === Content.card + n)
  }

  def goodVC6: Formula = {
    val C = Symbol("C")
    val C1 = Symbol("C1")
    val X = Symbol("X")
    val A0 = Symbol("A0")
    val A1 = Symbol("A1")
    val A2 = Symbol("A2")

    ((X.card === 1) && (X subseteq C) && (C1 seq C -- X) && ((A1 -- A0).card <= 1) && ((A2 -- A1).card <= C1.card)) implies ((A2 -- A1).card <= C.card)
  }

  def cornerCase: Formula = {
    (A1 ** A2).card =!= 0
  }

  /*
  def main(args: Array[String]): Unit = {
    //    val formulaList = List(goodVC6, goodVC4(3), form1, form2, form2a, form2b, form3, form3a, form3b, form4, form4b, form5, form6);
    //    formulaList.foreach ( v => verify(v) )
    verify(form1)
  }
  */

  def verify(form: Formula) = {
    form.print
    println

    val bapaForm = NormalForms.nnf(form)
    // val paForm = QFBAPAtoPATranslator(bapaForm)
    // val _ = PADecider.callSynth(paForm)
    // val withOutITEPAForm = QFBAPAtoPATranslator.rewriteITE(paForm)
    NormalForms.dnf(bapaForm).foreach(conj => {
      println("Conj = ")
      (And(conj)).print
      val paForm = NormalForms.nnf(QFBAPAtoPATranslator(And(conj), 0)._1)
      paForm.print
      Z3Converter.isSat(paForm) match {
        case Sat(t, _, _) => println("Formula satisfiable"); t()
        case Unsat => println("Formula unsatisfiable")
        case Z3Failure(e) => println("Z3 not executed.")
      }
    })
    ()
  }
}
