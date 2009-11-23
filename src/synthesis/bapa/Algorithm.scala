package synthesis.bapa

import scala.collection.mutable.Map
import scala.collection.immutable.Set
import java.lang.Integer

import ASTBAPASyn._

object Algorithm {
  def solve (t: Task, constrainOuterRegion: Boolean): (List[(String,PAInt)],Formula,List[String],List[SetAssignment]) = {
    val Task(x, y, k, l, f) = t

    val f1 = synthesis.bapa.Algorithm.step1(f)
    val (f2, mAll, vars) = synthesis.bapa.Algorithm.step2and3(f1, x ::: y)
    val (f3, listConstants) = synthesis.bapa.Algorithm.step4(mAll, x, constrainOuterRegion)
    val (f51, f52, f53) = synthesis.bapa.Algorithm.step5(x, y, k, l, vars, f2, f3, mAll, constrainOuterRegion)
    (listConstants, f51, f52, f53)
  }


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

  def createFormulaAboutCardinalityOfVennRegion(s: BASet, m: Map[String, Set[String]], i: Int): (Formula, String) = {
    val ls = getListofVennRegionsinS(s, m)
    val i1 = createSumOfCardinalitiesofVennRegions(ls)
    val c = "c" + i
    (FAtom(IntEqual(i1, IntVar(c))), c)
  }

  def isOnlyComplements(s: BASet): Boolean = s match {
    case SetVar(v) => false
    case Compl(SetVar(v)) => true
    case EmptySet => false
    case UnivSet => false
    case Intersec(s1, s2) => {
      val b1 = isOnlyComplements(s1) 
      val b2 = isOnlyComplements(s2)
      b1 && b2
    }
    case x@_ => error("Impossible case :" + x)  
  }



  def createListOfFormulasAboutVennRegions(l: List[BASet], m: Map[String, Set[String]], constrainOuterRegion: Boolean): 
   (List[Formula], List[(String, PAInt)]) = {
    var lf: List[Formula] = Nil
    var lt: List[(String, PAInt)] = Nil
    var i = 0
    l.foreach(s => {
      val (f, v) = createFormulaAboutCardinalityOfVennRegion(s, m, i)
      lf = f :: lf
      if (isOnlyComplements(s)) {
        lt = (v, IntConst(0)) :: lt
      } else {
        lt = (v, Card(s)) :: lt
      }
      i = i + 1
    })
    (lf, lt)
  }

  def createBigConjuctionOfFormulas(l: List[Formula]): Formula = {
    var f1 = l.head
    val t = l.tail
    t.foreach(e => f1 = And(f1, e))
    f1
  }

  def step4(m: Map[String, Set[String]], l: List[String], constrainOuterRegion: Boolean): (Formula, List[(String, PAInt)]) = { 
    val l0 = createListOfVennRegions(l)
    val ls = if (constrainOuterRegion) l0.filter(h => !(isOnlyComplements(h)))
      else l0
    val (lf, lt) = createListOfFormulasAboutVennRegions(ls, m, constrainOuterRegion)
    val ff = createBigConjuctionOfFormulas(lf) 
    (ff, lt)
  }

//--------------------------------------------



// ------------- Step 5


  def createFormulaToCallSynthesiser(vars: List[String], f: Formula, fQE: Formula): Formula = {
    var f1 = And(f, fQE)
    vars.foreach(v => { 
      val ft = FAtom(IntLessEqual(IntConst(0), IntVar(v)))
      f1 = And(ft, f1)
    })
    f1
  }


  def mapConnectingVariabes(vars: List[String]): Map[String, PAInt] = {
    val tm = Map[String, PAInt]()
    vars.foreach(e => {
      val pie = IntVar(e)
      tm += (e -> pie)
    })
    tm
  }


  def callArithmeticSynthesiser(inputVars: List[String], outputVars: List[String], f: Formula): Map[String, PAInt] = {
// do something, good man
// it should return something like (variable -> NameUnderWhichWasCalled)
// for example: val h00Var = {... code generating its value...}
// then h000 -> IntVar(h00Var)
    val m = mapConnectingVariabes(outputVars)
    m
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

  def outputValuesofSet(e: String, s: List[String], hValues: Map[String, PAInt], vRegions: Map[String, Set[String]], 
   i: Int, constrainOuterRegion: Boolean): (Int, List[SetAssignment]) = {
// e - output set variable who we are defining here
// s - already known set variables, hValues - values of h variables (h00 -> SetVar(h00V), etc.) 
// vRegions - aready existing a map saying which Venn region is contained in a set
// counting added sets
    val l0 = createListOfVennRegions(s)
    val l = if (constrainOuterRegion) l0.filter(h => !(isOnlyComplements(h)))
      else l0
    var k = i
    var listOfSets: List[String] = Nil
    var listOfAssigments: List[SetAssignment] = Nil 
    l.foreach(j => {
       val j1 = getListofVennRegionsinS(Intersec(j, SetVar(e)), vRegions)
       val dj = evaluateValuesofExpressions(j1, hValues)
       val nsv = "K" + k
       listOfSets = nsv :: listOfSets
       k = k + 1
       val t = Take(nsv, dj, j)
       listOfAssigments = t :: listOfAssigments
    })
    if (!(listOfSets.length == 0)) {
      if (listOfSets.length == 1) {
        val t = Simple(e, SetVar(listOfSets.head))
        listOfAssigments = t :: listOfAssigments
      } else {
        val s1 = listOfSets(0)
        val s2 = listOfSets(1)
        val lsn = listOfSets.drop(2)
        val nsv = "K" + k
        var sOld = nsv
        k = k + 1
        val t1 = Simple(nsv, Union(SetVar(s1), SetVar(s2)))
        listOfAssigments = t1 :: listOfAssigments
        lsn.foreach(u => {
          val nsv1 = "K" + k
          k = k + 1
          val t2 = Simple(nsv1, Union(SetVar(u), SetVar(sOld)))
          sOld = nsv1
          listOfAssigments = t2 :: listOfAssigments
        })
        val t3 = Simple(e, SetVar(sOld))
        listOfAssigments = t3 :: listOfAssigments
      }
    }
    (k, listOfAssigments.reverse)
  }


  def step5(x: List[String], y: List[String], k: List[String], l: List[String], vars: List[String],
   f: Formula, fQE: Formula, m: Map[String, Set[String]], constrainOuterRegion: Boolean): (Formula, List[String], List[SetAssignment]) = {
     val f1 = createFormulaToCallSynthesiser(vars, f, fQE)
     val outputVarsForMikael: List[String] = l ::: vars
     val m1 = callArithmeticSynthesiser(k, l ::: vars, f1)
     var s = x
     var listOfAssignments: List[SetAssignment] = Nil 
     var i = 0
     y.foreach(e => {
       val (j, tl) = outputValuesofSet(e, s, m1, m, i, constrainOuterRegion)
       listOfAssignments = listOfAssignments ::: tl
       s = e :: x
       i = j
     })
     (f1, outputVarsForMikael, listOfAssignments)
  }

}
