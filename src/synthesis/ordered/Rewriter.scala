package synthesis.ordered

import synthesis.ordered.OrderedTrees._
//import synthesis.bapa.{ASTBAPASyn => B}



object Rewriter {
  def algorithm(f: Formula) = {
    tempVarCount = 0
    val r = new Rewriter
    val g = r.decompose(f)
    (g, r.freshTermVars, r.freshSetVars)
  }

  // count for free variables
  private var tempVarCount = 0
}


class Rewriter {


  /**Decompose sets into integer and non-integer parts */

  def decompose(f: Formula) = f


  /**Guessing an ordering **/

  def guessorder(f0: Formula) = {
    val tformulas = freshTermVars.values.toList // map {case (_, v) => v}
    val sformulas = freshSetVars.values.toList // map {case (_, v) => v}
    val f = makeAnd(f0 :: tformulas ::: sformulas)

    val consts = constants(f).toList.sort {_ < _}.map {x => List(IntConst(x))}
    val elemvars = elemvariables(f).toList.sort {_ > _}.map {TermVar}
    val setvars = setvariables(f).toList.sort {_ < _}.map {SetVar}

    def rek(elems: List[TermVar], bi: List[List[PAInt]]): Unit = elems match {
      case Nil =>
        val bi1 = bi map {_ last}
        val classformula = makeAnd(
          for ((b, elems) <- bi1 zip bi; el <- elems.tail)
          yield TermEqual(el, b): Formula
          )
        val orderformula = if (bi.length < 2) True else makeAnd(
          for ((b, c) <- bi1 zip bi1.tail)
          yield TermLess(b, c)
          )
        println("visiting : " + bi)

        val ci = createSetvars(bi1)
        visit(bi1, ci, makeAnd(classformula, orderformula /*, cform*/ ))

      case e :: es =>
        rek(es, List(e) :: bi)
        for (i <- 0 until bi.length) {
          val (low, h :: high) = bi splitAt i
          rek(es, low ::: (e :: h) :: high)
          rek(es, low ::: h :: List(e) :: high)
        }
    }

    def createSetvars(bs: List[PAInt]): List[SetVar] = {
      //      println("class formula = " + cf)
      //      println("order formula = " + of)
      //      println()

      val classsetvars = bs map {
        _ =>
          freshSetSegment {ci => SetCard(ci, IntConst(1))}
      }

      val varsandvalues = bs zip classsetvars

      val neg1 = IntConst(-1)
      val first = freshSetSegment {c_nplus1 => True}
      val middle = for (((bimin1, cimin1), (bi, ci)) <- varsandvalues zip varsandvalues.tail) yield {
        freshSetSegment {ci => SetCard(ci, Plus(Minus(bi, bimin1), IntConst(-1)))}
      }
      val last = freshSetSegment {c_2nplus1 => True}
      classsetvars ::: first :: (middle ::: last :: Nil)
      // TODO domain segmentation ..
    }
    def visit(bs: List[PAInt], cs: List[SetVar], sideconstraint: Formula) = {
      makeAnd(for (svar <- setvars) yield {
        val as = for (ci <- cs) yield freshSetVar {
          ai =>
            SetEqual(ai, Intersec(svar, ci))
        }
        SetEqual(svar, makeUnion(as)): Formula
      })
    }


    rek(elemvars, consts)
  }


  def constants(f: Formula): Set[Int] = f match {
    case And(l, r) => constants(l) ++ constants(r)
    case Or(l, r) => constants(l) ++ constants(r)
    case Not(f) => constants(f)
    case FAtom(a) => constants(a)
  }

  def constants(a: Atom): Set[Int] = a match {
    case TermEqual(t1, t2) => constants(t1) ++ constants(t2)
    case TermLessEqual(t1, t2) => constants(t1) ++ constants(t2)
    case TermIsInt(t) => constants(t)
    case SetElem(t, _) => constants(t)
    case SetCard(_, t) => constants(t)
    case SetInf(_, t) => constants(t)
    case SetSup(_, t) => constants(t)
    case _ => Set.empty[Int]
  }

  def constants(t: PAInt): Set[Int] = t match {
    case IntConst(i) => Set(i)
    case Plus(t1, t2) => constants(t1) ++ constants(t2)
    case Times(_, t) => constants(t) // no need to add the coefficient
    case _ => Set.empty[Int]
  }

  def elemvariables(f: Formula): Set[String] = f match {
    case And(l, r) => elemvariables(l) ++ elemvariables(r)
    case Or(l, r) => elemvariables(l) ++ elemvariables(r)
    case Not(f) => elemvariables(f)
    case FAtom(a) => elemvariables(a)
  }

  def elemvariables(a: Atom): Set[String] = a match {
  //    case TermEqual(t1, t2) => elemvariables(t1) ++ elemvariables)
  //    case TermLessEqual(t1, t2) => elemvariables(t1) ++ elemvariables(t2)
  //    case TermIsInt(t) => elemvariables(t)
  //    case SetElem(t, _) => elemvariables(t)
  //    case SetCard(_, t) => elemvariables(t)
    case SetInf(_, t) => elemvariables(t)
    case SetSup(_, t) => elemvariables(t)
    case _ => Set.empty[String]
  }

  def elemvariables(t: PAInt): Set[String] = t match {
    case TermVar(id) => Set(id)
    case Plus(t1, t2) => elemvariables(t1) ++ elemvariables(t2)
    case Times(_, t) => elemvariables(t)
    case _ => Set.empty[String]
  }

  def setvariables(f: Formula): Set[String] = f match {
    case And(l, r) => setvariables(l) ++ setvariables(r)
    case Or(l, r) => setvariables(l) ++ setvariables(r)
    case Not(f) => setvariables(f)
    case FAtom(a) => setvariables(a)
  }

  def setvariables(a: Atom): Set[String] = a match {
    case SetEqual(s1, s2) => setvariables(s1) ++ setvariables(s2)
    case SetLess(s1, s2) => setvariables(s1) ++ setvariables(s2)
    case SetElem(_, s) => setvariables(s)
    case SetIsInfinite(s) => setvariables(s)
    case SetCard(s, _) => setvariables(s)
    case SetInf(s, _) => setvariables(s)
    case SetSup(s, _) => setvariables(s)
    case _ => Set.empty[String]
  }

  def setvariables(s: BASet): Set[String] = s match {
    case SetVar(id) => Set(id)
    case Union(s1, s2) => setvariables(s1) ++ setvariables(s2)
    case Intersec(s1, s2) => setvariables(s1) ++ setvariables(s2)
    case Compl(s) => setvariables(s)
    case Take(_, s2) => setvariables(s)
    case _ => Set.empty[String]
  }



  // Fresh name generator
  var freshTermVars = Map.empty[String, Formula]
  var freshSetVars = Map.empty[String, Formula]
  var tempSegmentCount = 0

  def freshTermVar(t: TermVar => Formula) = {
    Rewriter.tempVarCount += 1
    val v = ".t" + Rewriter.tempVarCount
    freshTermVars += ((v, t(TermVar(v))))
    TermVar(v)
  }

  def freshSetVar(s: SetVar => Formula) = {
    Rewriter.tempVarCount += 1
    val v = ".s" + Rewriter.tempVarCount
    freshSetVars += ((v, s(SetVar(v))))
    SetVar(v)
  }

  def freshSetSegment(s: SetVar => Formula) = {
    tempSegmentCount += 1
    val v = ".C" + tempSegmentCount
    freshSetVars += ((v, s(SetVar(v))))
    SetVar(v)
  }
}
