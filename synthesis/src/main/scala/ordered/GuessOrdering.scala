package synthesis.ordered

import AST._
import Primitives._


object GuessOrdering {
  import scala.collection.mutable.{ArrayBuffer, HashMap => MutableMap, HashSet => MutableSet, ListBuffer}

  /**Extract variables  & inf/sup expressions **/

  def intvars = variablesOf(_ == IntType)

  def setvars = variablesOf(_ == SetType)

  private def variablesOf(pred: Type => Boolean) = {
    val empty: Set[Ident] = Set.empty
    def vars(f: Formula): Set[Ident] = f match {
      case True | False => empty
      case Not(f) => vars(f)
      case And(fs) => (empty /: fs) {_ ++ vars(_)}
      case Or(fs) => (empty /: fs) {_ ++ vars(_)}
      case Predicate(_, ts) => (empty /: ts) {_ ++ tvars(_)}
    }
    def tvars(t: Term): Set[Ident] = t match {
      case id@Ident(t, _) if pred(t) => Set(id)
      case Op(_, ts) => (empty /: ts) {_ ++ tvars(_)}
      case _ => empty
    }
    vars _
    //    (f: Formula) => vars(f).toList sortWith (_.name < _.name)
  }

  private def set2list(set: Set[Ident]) = set.toList sortWith (_.name.name < _.name.name)

  private def findInf(f: Formula): List[(SetVar, IntVar)] = f match {
    case Predicate(EQ, List(term@Ident(IntType, _), Op(INF, List(set@Ident(SetType, _))))) =>
      List((set, term))
    case _ => Nil
  }

  private def findSup(f: Formula): List[(SetVar, IntVar)] = f match {
    case Predicate(EQ, List(term@Ident(IntType, _), Op(SUP, List(Ident(SetType, set))))) =>
      List((set, term))
    case _ => Nil
  }

  /* Predicate for removing the inf and sup references from a pure and flat formula */
  private def isInfOrSup(f: Formula) = f match {
    case Predicate(EQ, List(Ident(IntType, _), Op(INF | SUP, List(Ident(SetType, _))))) => true
    case _ => false
  }


  /**Guessing **/

  private def pickOne[A](list: List[A]): List[(List[A], A, List[A])] = {
    val front = new ListBuffer[A]
    var back = list
    val buffer = new ListBuffer[(List[A], A, List[A])]
    while (back != Nil) {
      val elem = back.head
      back = back.tail

      buffer += ((front toList, elem, back))
      front += elem
    }
    buffer.toList
  }

  def guess(conj: List[Formula]) = {
    val search = new Search(conj)
    val equivMap = new MutableMap[IntVar, Int]
    var total = 0
    var count = 0
    var str = ""

    def guessSet(setvars: List[SetVar]): Unit = {
      setvars match {
        case sv :: svs =>
          // Guess empty
          search.addLevel
          search += sv.card === 0
          guessSet(svs)
          search.removeLevel

          // Guess non-empty
          search.addLevel
          search += sv.card >= 1
          val inff = Ident(IntType, Symbol.infOf(sv))
          val supf = Ident(IntType, Symbol.supOf(sv))
          search.infmap += sv -> inff
          search.supmap += sv -> supf
          search.termmap += inff -> new Node(inff)
          search.termmap += supf -> new Node(supf)
          search.addLE(inff, supf)

          guessSet(svs)

          search.infmap -= sv
          search.supmap -= sv
          search.termmap -= inff
          search.termmap -= supf
          search.removeLevel

        case Nil =>
          guessOrdering
      }
    }

    // FIXME: Warning, ugly code !
    def guessOrderRek(current: List[Node], after: List[Node], bi: List[IntVar]) {
      println("  REK ( " + current.map {_.toStr} + ",  " + after.map {_.toStr} + " , " + bi.map {_.name.toString})
      if (current.isEmpty && after.isEmpty) {
        total += 1
        segmentation(bi.reverse)

        //search.mkFormula.print
        if (TestApp.test2(search.mkFormula)) {
          count += 1
          //          println("Formula " + count + " / " + total)
          //          println("Level " + search.level + ",  " + search.formulas)
          //search.mkFormula.print
          //println
        } else {
          println("Synthesis derived false as a precondition. Is it possible to prune ?")
        }
      } else {
        // guess same equivalence class
        for ((front, node, back) <- pickOne(current)) {
          //        var list1 = current
          //        var list2 = Nil: List[Node]
          //        while (!list1.isEmpty) {
          //          val node = list1.head
          println("    GUESS SAME " + node.tvar.name)

          search.addLevel
          search += bi.head === node.tvar
          equivMap(node.tvar) = bi.length
          val (nodes, nextnodes) = node.visit
          guessOrderRek(back ::: nodes, front ::: after ::: nextnodes, bi)
          node.unvisit
          search.removeLevel

          //          list2 = node :: list2
          //          list1 = list1.tail
        }
        // guess next equivalence class
        for ((front, node, back) <- pickOne[Node](current ::: after)) {
          //        list1 = current ::: after
          //        list2 = Nil: List[Node]
          //        while (!list1.isEmpty) {
          //          val node = list1.head
          println("    GUESS NEXT " + node.tvar.name)

          search.addLevel
          search += bi.head < node.tvar
          equivMap(node.tvar) = bi.length + 1
          val (nodes, nextnodes) = node.visit
          guessOrderRek(back ::: nodes, front ::: nextnodes, node.tvar :: bi)
          node.unvisit
          search.removeLevel

          //          list2 = node :: list2
          //          list1 = list1.tail
        }
      }
    }

    def guessOrdering {
      val nodes = (for ((term, node) <- search.termmap; if node.inDegree == 0)
      yield node).toList

      //      println("  REK ( " + nodes.map{_.toStr} + " )")
      str = str + "\n  #nodes = " + nodes.size + "  (" + count + ")"

      // guess first equivalence class
      for ((front, node, back) <- pickOne(nodes)) {
        //var list1 = nodes
        //var list2 = Nil: List[Node]
        //while (!list1.isEmpty) {
        //  val node = list1.head

        search.addLevel
        val (nodes, nextnodes) = node.visit
        equivMap(node.tvar) = 1
        guessOrderRek(back ::: nodes, front ::: nextnodes, node.tvar :: Nil)
        node.unvisit
        search.removeLevel

        //   list2 = node :: list2
        //   list1 = list1.tail
      }
    }

    def segmentation(_b: List[IntVar]) {
      val n = _b.length
      val b = (null :: _b).toArray

      // TODO remove assert
      for (i <- 1 to n)
        if (i != equivMap(b(i))) error(i + " != " + equivMap(b(i)))

      def newAvar(svar: Ident)(i: Int) = Ident(SetType, Symbol.partClass(svar, i))
      def newBvar(svar: Ident)(i: Int) = Ident(SetType, Symbol.partRange(svar, i))
      def newCvar(i: Int) = Ident(SetType, Symbol.equiClass(i))
      def newDvar(i: Int) = Ident(SetType, Symbol.equiRange(i))

      //      val max = Ident(IntType, Symbol.fresh("max"))
      //      val min = Ident(IntType, Symbol.fresh("min"))
      //      val map = new MutableMap[SetVar,List[SetVar]]
      //      if (n > 0) {
      //        search += max === MAX
      //        search += min === MIN
      //      }
      // Cardinality constraints on C-vars
      val Cvars = ((0 to n) map newCvar).toArray
      val Dvars = ((0 to n) map newDvar).toArray
      //      for (i <- 1 to n) search += Cvars(i).card === 1
      //      search += Dvars(0).card === 0
      //      search += Dvars(0).card === ((b(1) - min) - 1)
      //      for (i <- 1 to (n - 1)) search += Dvars(i).card === ((b(i + 1) - b(i)) - 1)
      //      search += Dvars(n).card === ((max - b(n)) - 1)
      //      search += Dvars(n).card === 0

      // Partitioning constraints on Ai-vars
      for (A <- search.infmap.keySet) {
        val Avars = ((0 to n) map newAvar(A)).toArray
        val Bvars = ((0 to n) map newBvar(A)).toArray
        //        for (i <- 1 to n) search += Avars(i) seq (A ** Cvars(i))
        //        for (i <- 1 to (n - 1)) search += Bvars(i) seq (A ** Dvars(i))
        val Avars_ = Avars.toList.tail ::: Bvars.toList.tail.init
        search += A seq Op(UNION, Avars_)
        //        map += a -> aivars

        // println("Set " + A + " lower=" + equivMap(search infmap A) + "(" +
        //        (search infmap A) + ") upper=" + equivMap(search supmap A) + "(" + (search supmap A) + ") ")
        val infp = equivMap(search infmap A) - 1
        val supp = equivMap(search supmap A) + 1
        val set = MutableSet[Ident]()
        for (i <- 1 to infp) set += Avars(i)
        for (i <- supp to n) set += Avars(i)
        for (i <- 1 to infp) set += Bvars(i)
        for (i <- supp to n) set += Bvars(i - 1)
        //search.subst(id => if (set(id)) emptyset else id)
        search.remove(set)
      }
    }

    //    println
    //    println(search.freeSetvars)
    //    search.termmap.values.toList foreach println
    //    println

    guessSet(search.freeSetvars)
    println(str)
    println("[  #svars = " + search.freeSetvars.size + "  (" + count + ") ]")
  }


  def removePartition(set: (Ident => Boolean)) = {
    def substf(form: Formula): Formula = form match {
      case True | False => form
      case Not(f) => !substf(f)
      case And(fs) => And(fs map substf)
      case Or(fs) => Or(fs map substf)
      case Predicate(SEQ, List(id@Ident(_, _), _)) if set(id) => True
      case Predicate(c, ts) => Predicate(c, ts map substt)
    }
    def substt(term: Term): Term = term match {
      case id@Ident(_, _) => if (set(id)) emptyset else term
      case Lit(_) => term
      case Op(ITE(f), ts) => Op(ITE(substf(f)), ts map substt)
      case Op(p, ts) => Op(p, ts map substt)
    }
    substf _
  }

  def substitute(map: (Ident => Term)) = {
    def substf(form: Formula): Formula = form match {
      case True | False => form
      case Not(f) => !substf(f)
      case And(fs) => And(fs map substf)
      case Or(fs) => Or(fs map substf)
      case Predicate(c, ts) => Predicate(c, ts map substt)
    }
    def substt(term: Term): Term = term match {
      case id@Ident(_, _) => map(id)
      case Lit(_) => term
      case Op(ITE(f), ts) => Op(ITE(substf(f)), ts map substt)
      case Op(p, ts) => Op(p, ts map substt)
    }
    substf _
  }

  // private val MAX = Integer.MAX_VALUE / 2
  // private val MIN = -MAX

  private class Node(val tvar: IntVar) {
    var outArcs: List[Node] = Nil
    var strictOutArcs: List[Node] = Nil
    var inDegree = 0

    def decr = {
      inDegree -= 1
      inDegree == 0
    }

    def incr {inDegree += 1}

    def visit = {
      val current = for (node <- outArcs; if node.decr) yield node
      val after = for (node <- strictOutArcs; if node.decr) yield node
      //      println("VISIT " + tvar.name.toString + "   " + (current, after))
      (current, after)
    }

    def unvisit = {
      for (node <- outArcs) node.incr
      for (node <- strictOutArcs) node.incr
    }

    override def toString = "" + tvar.name + " #" + inDegree + outArcs.map {_.tvar.name}.mkString("   <= [", ",", "] ") + strictOutArcs.map {_.tvar.name}.mkString(" < [", ",", "]")

    def toStr = "" + tvar.name + " #" + inDegree
  }

  /**Search **/

  type IntVar = Ident
  type SetVar = Ident

  private class Search(conjunction: List[Formula]) {
    var level = 0
    val formulas = new ArrayBuffer[List[Formula]]
    val termmap = new MutableMap[IntVar, Node]()
    val infmap = new MutableMap[SetVar, IntVar]()
    val supmap = new MutableMap[SetVar, IntVar]()
    val (freeSetvars, boundvars) = init

    private def init = {
      val f0 = conjunction remove isInfOrSup
      val infs = conjunction flatMap findInf
      val sups = conjunction flatMap findSup

      addLevel
      this ++= f0
      for (entry@(svar, tvar1) <- infs) infmap get svar match {
        case Some(tvar2) => this += (tvar1 === tvar2)
        case None => infmap += entry
      }
      for (entry@(svar, tvar1) <- sups) supmap get svar match {
        case Some(tvar2) => this += (tvar1 === tvar2)
        case None => supmap += entry
      }
      for (svar <- (Set.empty ++ infmap.keySet) -- supmap.keySet) {
        supmap += svar -> Ident(IntType, Symbol.supOf(svar))
      }
      for (svar <- (Set.empty ++ supmap.keySet) -- infmap.keySet) {
        infmap += svar -> Ident(IntType, Symbol.infOf(svar))
      }
      val freeSetvars = (setvars(And(conjunction)) -- infmap.keySet).toList
      val boundvars = (Set.empty ++ infmap.values ++ supmap.values).toList

      for (tvar <- boundvars) {
        termmap += tvar -> new Node(tvar)
      }
      for (svar <- infmap.keySet) {
        addLE(infmap(svar), supmap(svar))
        //        println("********* addLE( " + infmap(svar)+", "+supmap(svar)+")")
      }
      for (f <- f0) f match {
      // TODO remove matched predicates from formula ?
        case Predicate(LT, List(Ident(_, t1), Ident(_, t2))) => addLT(t1, t2) ///; println("Add " + f)
        case Predicate(GT, List(Ident(_, t1), Ident(_, t2))) => addLT(t2, t1) //; println("Add " + f)
        case Predicate(LE, List(Ident(_, t1), Ident(_, t2))) => addLE(t1, t2) //; println("Add " + f)
        case Predicate(GE, List(Ident(_, t1), Ident(_, t2))) => addLE(t2, t1) //; println("Add " + f)
        case _ =>
      }
      (freeSetvars, boundvars)
    }

    def addLE(t1: IntVar, t2: IntVar): Unit = (termmap get t1, termmap get t2) match {
      case (Some(n1), Some(n2)) =>
        n1.outArcs = n2 :: n1.outArcs
        n2.incr
      case x => error(x toString)
    }

    def addLT(t1: IntVar, t2: IntVar): Unit = (termmap get t1, termmap get t2) match {
      case (Some(n1), Some(n2)) =>
        n1.strictOutArcs = n2 :: n1.strictOutArcs
        n2.incr
      case x => error(x toString)
    }

    def addLevel {
      formulas += Nil
      level += 1
    }

    def removeLevel {
      level -= 1
      formulas remove level
    }

    def +=(f: Formula) {
      formulas(level - 1) = f :: formulas(level - 1)
    }

    def ++=(f: Iterable[Formula]) {
      formulas(level - 1) = f.toList ::: formulas(level - 1)
    }

    /* def subst(sub: (Ident => Term)) {
     formulas(level - 1) = formulas(level - 1) map substitute(sub)
   } */

    def remove(set: (Ident => Boolean)) {
      formulas(level - 1) = formulas(level - 1) map removePartition(set)
    }

    def mkFormula = NormalForms.nnf(And(formulas.toList flatMap {x => x.reverse}))
  }


}
