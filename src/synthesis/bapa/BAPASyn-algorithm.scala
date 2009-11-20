package synthesis.bapa

import scala.collection.mutable.Map
import scala.collection.immutable.Set
import java.lang.Integer

object Algorithm {

// -------------- Step 1

  def removeSetEqulitiesInAtom(a: Atom): Formula = a match {
    case SetEqual(s1, s2) => 
      And(FAtom(SetSubset(s1, s2)), FAtom(SetSubset(s2, s1)))
    case _ =>  FAtom(a)
  }

  def removeSetEqulities(f: Formula): Formula = f match {
    case And(f1, f2) => {
      val f1n = removeSetEqulities(f1)
      val f2n = removeSetEqulities(f2)
      And(f1n, f2n)
    }
    case Or(f1, f2) => {
      val f1n = removeSetEqulities(f1)
      val f2n = removeSetEqulities(f2)
      Or(f1n, f2n)
    }
    case Not(f1)  => {
      val f1n = removeSetEqulities(f1)
      Not(f1n)
    }
    case FAtom(a)  => removeSetEqulitiesInAtom(a)
  }


  def removeSetSubsetsInAtom(a: Atom): Formula = a match {
    case SetSubset(s1, s2) => 
      FAtom(IntEqual(Card(Intersec(s1, Compl(s2))), IntConst (0)))
    case _ =>  FAtom(a)
  }


  def removeSetSubsets(f: Formula): Formula = f match {
    case And(f1, f2) => {
      val f1n = removeSetSubsets(f1)
      val f2n = removeSetSubsets(f2)
      And(f1n, f2n)
    }
    case Or(f1, f2) => {
      val f1n = removeSetSubsets(f1)
      val f2n = removeSetSubsets(f2)
      Or(f1n, f2n)
    }
    case Not(f1)  => {
      val f1n = removeSetSubsets(f1)
      Not(f1n)
    }
    case FAtom(a)  => removeSetSubsetsInAtom(a)
  }

  def step1(f: Formula): Formula = {
    val f1 = removeSetEqulities(f)
    val f2 = removeSetSubsets(f1)
    f2
  }

//--------------------------------------------

// ------------- Step 2 and 3 together


  def power2(n: Int): Int = {
    var i = 1
    for(k <- 1 to n) i = i * 2
    i
  }

  def createListOfBinaryNumbersFrom0To2ExpN(n: Int): List[List[String]] = {
    if (n == 0) Nil
    else {
      val ub = power2 (n - 1)
      var l1: List[List[String]] = Nil
      for (i <- 0 to (ub - 1) ) {
        val s = (Integer.toBinaryString(i)).toList
        var s1 = s.map (_.toString)
        while (s1.length < (n - 1)) {
          s1 = "0" :: s1
        }
        l1 = s1 :: l1
      }
      l1
    }
  }

  def createStringfromList(i: Int, l: List[String]): String = {
    val ln = l.take(i) ::: ( "1" :: l.drop(i) )
    ln.mkString("R", "", "")
  }


  def createVennRegionsForSet(i: Int, l: List[List[String]]): Set[String] = {
    var s = Set[String]()
    l.foreach(l1 => {
      val st = createStringfromList(i, l1)
      s = s ++ Set(st)
    })
    s
  }

  def createVennRegionsForUniversalSet(l: List[List[String]]): Set[String] = {
    var s = Set[String]()
    l.foreach(e => {
      val l0 = "0" :: e
      val s0 = l0.mkString("R", "", "")
      s = s ++ Set(s0)
      val l1 = "1" :: e
      val s1 = l1.mkString("R", "", "")
      s = s ++ Set(s1)
    })
    s
  }

  def createMap0fVennRegions(l: List[String]): Map[String, Set[String]] = { 
    val tm = Map[String, Set[String]]()
    val n = l.length
    var i = 0
    val ls = createListOfBinaryNumbersFrom0To2ExpN(n)
    l.foreach(e => {
      val nl = createVennRegionsForSet(i, ls)
      i = i + 1
      tm += (e -> nl)
      }
    )
    val us = createVennRegionsForUniversalSet(ls)
    tm += ("ALL" -> us)
    tm
  }


  def getListofVennRegionsinS(s: BASet, m: Map[String,Set[String]]): Set[String]  = s match {
    case SetVar(v) => m(v)
    case EmptySet => Set[String]()
    case UnivSet => m("ALL")
    case Union(s1, s2) => {
      val ss1 = getListofVennRegionsinS(s1, m)
      val ss2 = getListofVennRegionsinS(s2, m)
      ss1 ++ ss2
    }
    case Intersec(s1, s2) => {
      val ss1 = getListofVennRegionsinS(s1, m)
      val ss2 = getListofVennRegionsinS(s2, m)
      val ss3 = ss1.intersect(ss2)
      ss3
    }
    case Compl(s1) => {
      val ss1 = getListofVennRegionsinS(s1, m)
      val ss2 = m("ALL") -- ss1
      ss2
    }
  }

  def createCardinalityOfVennRegion(s: String): PAInt = {
    val s1 = s.replace('R', 'h')
    IntVar(s1)
  }

  def createSumOfCardinalitiesofVennRegions(s: Set[String]): PAInt =  {
    val l = s.toList
    if (l.isEmpty) IntConst(0) else {
       var ts = createCardinalityOfVennRegion(l.head)
       val t = l.tail
       t.foreach(e => {
         val ns = createCardinalityOfVennRegion(e)
         ts = Plus(ts, ns)
       })
       ts
    }
  }

  def replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i: PAInt, m: Map[String,Set[String]]): PAInt  = i match {
    case IntVar(v) => i
    case IntConst(c) => i
    case Plus(i1, i2) => {
      val i1n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i1, m)
      val i2n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i2, m)
      Plus(i1n, i2n)
    }
    case Times(c, i1) => {
      val i1n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i1, m)
      Times(c, i1n)
    }
    case Card(s) => {
      val ls = getListofVennRegionsinS(s, m)
      val i1 = createSumOfCardinalitiesofVennRegions(ls)
      i1
    }
  }


  def replaceSetsWithDijointUnionsAndRemoveCardinalitiesinAtom(a: Atom, m: Map[String,Set[String]]): Atom  = a match {
    case IntEqual(i1, i2) => {
      val i1n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i1, m)
      val i2n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i2, m)
      IntEqual(i1n, i2n)
    }
    case IntLessEqual(i1, i2) => {
      val i1n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i1, m)
      val i2n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i2, m)
      IntLessEqual(i1n, i2n)
    }
    case IntDivides(c, i1) => {
      val i1n = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinInt(i1, m)
      IntDivides(c, i1n)
    }
    case x@_ => error("Impossible case :" + x)  
  }

  def replaceSetsWithDijointUnionsAndRemoveCardinalities(f: Formula, m: Map[String,Set[String]]): Formula = f match {
    case And(f1, f2) => {
      val f1n = replaceSetsWithDijointUnionsAndRemoveCardinalities(f1, m)
      val f2n = replaceSetsWithDijointUnionsAndRemoveCardinalities(f2, m)
      And(f1n, f2n)
    }
    case Or(f1, f2) => {
      val f1n = replaceSetsWithDijointUnionsAndRemoveCardinalities(f1, m)
      val f2n = replaceSetsWithDijointUnionsAndRemoveCardinalities(f2, m)
      Or(f1n, f2n)
    }
    case Not(f1) => {
      val f1n = replaceSetsWithDijointUnionsAndRemoveCardinalities(f1, m)
      Not(f1n)
    }
    case FAtom(a) =>{
      val an = replaceSetsWithDijointUnionsAndRemoveCardinalitiesinAtom(a, m)
      FAtom(an)
    } 
  }

  def cardinalitiesOfVennRegions(m: Map[String, Set[String]]): List[String] = {
    val s = m("ALL")
    val l = s.toList
    val l1 = l.map(s1 => s1.replace("R", "h"))
    l1
  }

  def step2and3(f: Formula, l: List[String]): (Formula, Map[String, Set[String]], List[String]) = { 
    val m = createMap0fVennRegions(l)
    val f1 = replaceSetsWithDijointUnionsAndRemoveCardinalities(f, m)
    val v = cardinalitiesOfVennRegions(m)
    (f1, m, v)
  }


//--------------------------------------------



// ------------- Step 4

  def createListOfSetsAndComplements(s: List[String], l: List[String]): List[BASet] = {
    var l1: List[BASet] = Nil 
    var i = 0
    s.foreach(e => {
      val v = SetVar(l(i))
      val st = if (e == "0") Compl(v) else v
      i = i + 1
      l1 = st :: l1
    })
    l1
  }

  def createBigIntersection(l: List[BASet]): BASet = {
    if (l.isEmpty) EmptySet else {
       var s1 = l.head
       val t = l.tail
       t.foreach(e => s1 = Intersec(s1, e))
       s1
    }
  }

  def createVennRegionFrom01List(s: List[String], l: List[String]): BASet = {
    val l1 = createListOfSetsAndComplements(s, l)
    val l2 = createBigIntersection(l1)
    l2
  }

  def createListOfVennRegions(l: List[String]): List[BASet] = {
    val n = l.length
    val l1 = createListOfBinaryNumbersFrom0To2ExpN(n + 1)
    var l2: List[BASet] = Nil
    l1.foreach(s => {
      val vr = createVennRegionFrom01List(s, l)
      l2 = vr :: l2
    })
    l2
  }

  def createFormulaAboutCardinalityOfVennRegion(s: BASet, m: Map[String, Set[String]]): Formula = {
    val ls = getListofVennRegionsinS(s, m)
    val i1 = createSumOfCardinalitiesofVennRegions(ls)
    FAtom(IntEqual(i1, Card(s)))
  }

  def createListOfFormulasAboutVennRegions(l: List[BASet], m: Map[String, Set[String]]): List[Formula] = {
    var lf: List[Formula] = Nil
    l.foreach(s => {
      val f = createFormulaAboutCardinalityOfVennRegion(s, m)
      lf = f :: lf})
    lf
  }

  def createBigConjuctionOfFormulas(l: List[Formula]): Formula = {
    var f1 = l.head
    val t = l.tail
    t.foreach(e => f1 = And(f1, e))
    f1
  }

  def step4(m: Map[String, Set[String]], l: List[String]): Formula = { 
    val ls = createListOfVennRegions(l)
    val lf = createListOfFormulasAboutVennRegions(ls, m)
    val ff = createBigConjuctionOfFormulas(lf) 
    ff
  }

//--------------------------------------------



// ------------- Step 5



  // k - list of input var. names, l - list of output var. names
  // f - formula result of translation,  fQE - formula result of "quantifier elimination"
  // return map that  has keeps values of l, vars
  def callArithmeticSynthesiser(k: List[String], l: List[String], vars: List[String], f: Formula, fQE: Formula): Map[String, PAInt] = {

       NNNNNN = synthesis.PASynthesis.solve()
  }


  def createBigSumOfIntegers(l: List[PAInt]): PAInt = {
    var l1 = l.head
    val t = l.tail
    t.foreach(e => l1 = Plus(l1, e))
    l1
  }



  def evaluateValuesofExpressions(s: Set[String], hValues: Map[String, PAInt]): PAInt = {
// (R100, R001 R010) and returns h100 + h001 + h010
    val l = s.toList
    if (l.isEmpty) IntConst(0) else {
      val l1 = l.map(e => e.replace('R', 'h'))
      val l2 = l1.map(e => hValues(e))
      val t = createBigSumOfIntegers(l2)
      t
    }
  }

  def outputValuesofSet(e: String, s: List[String], hValues: Map[String, PAInt], vRegions: Map[String, Set[String]], i: Int): (Int, List[SetAssignment]) = {
    val l = createListOfVennRegions(s)
    var k = i
    var listOfSets: List[String] = Nil
    l.foreach(j => {
       val j1 = getListofVennRegionsinS(Intersec(j, SetVar(e)), vRegions)
       val dj = evaluateValuesofExpressions(j1, hValues)
       if (!(dj == IntConst(0))) {
         val nsv = "K" + j
         listOfSets = nsv :: listOfSets
         k = k + 1
         if (dj == Card(j)) {
            print("val " + nsv + " = ")
            synthesis.bapa.Printer.print_Set(j)
            println(" ")
         } else {
            print("val " + nsv + " = first(")
            synthesis.bapa.Printer.print_Int(dj)
            print(", ")
            synthesis.bapa.Printer.print_Set(j)
            println(" ")
         }
      }
    })
    if (!(listOfSets.isEmpty)) {
      print("val " + e + " = " + listOfSets.head)
      val t = listOfSets.tail
      t.foreach(w => print(" UNION ") + w)
      println(" ")
    }
    k
  }


  def step5(x: List[String], y: List[String], k: List[String], l: List[String], vars: List[String],
   f: Formula, fQE: Formula, m: Map[String, Set[String]]): List[SetAssignment] = {
     val m1 = callArithmeticSynthesiser(k, l, vars, f, fQE)
     var s = x
     var i = 0
     y.foreach(e => {
       i = outputValuesofSet(e, s, m1, m, i)
       s = e :: x
     })
     println("finished!")
  }

}
