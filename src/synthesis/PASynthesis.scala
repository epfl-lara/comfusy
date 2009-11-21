package synthesis
//import scala.annotation.tailrec

//*********************************** Pressburger Synthesis ************************************************//


object PASynthesis {
    /// ************* Abstract syntax tree ***************///
  abstract class PAVariable
  case class InputVar(name: String) extends PAVariable {
    // Syntactic sugar
    def +(pac : PACombination) = pac+PACombination(this)
    def +(v : InputVar) = PACombination(v)+PACombination(this)
    def +(v : OutputVar) = PACombination(v)+PACombination(this)
    def *(i : Int) = PACombination(i, this)
  }
  case class OutputVar(name: String) extends PAVariable {
    // Syntactic sugar
    def +(pac : PACombination) = pac+PACombination(this)
    def +(v : InputVar) = PACombination(v)+PACombination(this)
    def +(v : OutputVar) = PACombination(v)+PACombination(this)
    def *(i : Int) = PACombination(i, this)
  }

  abstract sealed class PAExpression {
    def output_variables:List[OutputVar] = this match {
      case PACombination(c, i, o) => o map (_._2)
      case PADivides(c, pac) => pac.output_variables
      case PAEqualZero(pac) => pac.output_variables
      case PAGreaterZero(pac) => pac.output_variables
      case PAGreaterEqZero(pac) => pac.output_variables
      case PATrue() => Nil
      case PAFalse() => Nil
      case PADivision(pac, n) => pac.output_variables
      case PADisjunction(l) => (l flatMap (_.output_variables)).removeDuplicates
      case PAConjunction(l) => (l flatMap (_.output_variables)).removeDuplicates
      case PAMinimum(l) => (l flatMap (_.output_variables)).removeDuplicates
      case PAMaximum(l) => (l flatMap (_.output_variables)).removeDuplicates
    }
    def input_variables:List[InputVar] = this match {
      case PACombination(c, i, o) => i map (_._2)
      case PADivides(c, pac) => pac.input_variables
      case PAEqualZero(pac) => pac.input_variables
      case PAGreaterZero(pac) => pac.input_variables
      case PAGreaterEqZero(pac) => pac.input_variables
      case PATrue() => Nil
      case PAFalse() => Nil
      case PADivision(pac, n) => pac.input_variables
      case PADisjunction(l) => (l flatMap (_.input_variables)).removeDuplicates
      case PAConjunction(l) => (l flatMap (_.input_variables)).removeDuplicates
      case PAMinimum(l) => (l flatMap (_.input_variables)).removeDuplicates
      case PAMaximum(l) => (l flatMap (_.input_variables)).removeDuplicates
    }
    def has_output_variables: Boolean = (output_variables != Nil) //OptimizeMe!
    /// Simplified version of this expression
    def simplified: PAExpression
    def replace(y: PAVariable, t: PACombination): PAExpression
     
    override def toString = toScalaString
    
    def toScalaString = this match {
      case PADivides(n, pac) => val pac_s = pac.toNiceString
        if(((pac_s indexOf '-') >= 0) || ((pac_s indexOf '+') >= 0))
          ("("+ pac_s + ") % " + n + " == 0")
        else
          (pac_s + " % " + n + " == 0")
      case PAEqualZero(pac) => pac.toString + " == 0"
      case PAGreaterZero(pac) => pac.toString + " > 0"
      case PAGreaterEqZero(pac) => pac.toString + " >= 0"
      case PADivision(numerator, denominator) => val string_numerator = numerator.toString
        //if((string_numerator indexOf '-') >=0  || (string_numerator indexOf '+') >=0) {
          "("+ string_numerator + "- ("+denominator+" + ("+string_numerator+")%"+denominator+")%"+denominator+")/" + denominator
        //} else {
        //  string_numerator +"/"+ denominator
        //}
      case PAMinimum(l) => "Math.min(" + (l map (_.toString) reduceLeft(_ + ", " + _)) + ")"
      case PAMaximum(l) => "Math.max(" + (l map (_.toString) reduceLeft(_ + ", " + _)) + ")"
      case pac@PACombination(_, _, _) => pac.toNiceString
      case PATrue() => "true"
      case PAFalse() => "false"
      case PAConjunction(eqs) => eqs match {
        case Nil => "true"
        case (a::Nil) => a.toString
        case l => l map (_ match {
          case t if t.isInstanceOf[PAEquation] => t.toString
          case pac@PAConjunction(_) => pac.toString
          case t => "("+t.toString+")"
         }
        ) reduceLeft (_+ " && " + _)
      }
      case PADisjunction(eqs) => eqs match {
        case Nil => "false"
        case (a::Nil) => a.toString
        case l => l map (_ match {
          case t if t.isInstanceOf[PAEquation] => t.toString
          case pac@PADisjunction(_) => pac.toString
          case t => "("+t.toString+")"
         }
        ) reduceLeft (_+ " || " + _)
      }
      case _ => super.toString
    }
  }
  
  abstract sealed class PAFormula extends PAExpression {
    def replace(y: PAVariable, t: PACombination): PAFormula
    def replaceList(lxt : List[(PAVariable, PACombination)]): PAFormula = {
      lxt.foldLeft(this){ case (result, (x, t)) => result.replace(x, t) }
    }
    
    // This matching IS exhaustive since other matches are made if this is an atomic equation
    def simplified: PAFormula = this match {
      case PAConjunction(eqs) => val eqs_simplified = eqs map (_.simplified)
      eqs_simplified match {
        case Nil => PATrue()
        case l if l contains PAFalse() => PAFalse()
        case l => l remove (_ == PATrue()) match {
          case Nil => PATrue()
          case (a::Nil) => a
          case l => PAConjunction(l) 
        }
      }
      case PADisjunction(eqs) => eqs map (_.simplified) match {
        case Nil => PAFalse()
        case l if l contains PATrue() => PATrue()
        case l =>  l remove (_ == PAFalse()) match {
          case Nil => PAFalse()
          case (a::Nil) => a
          case l => PADisjunction(l) 
        }
      }
      case _ => throw new Error("Simplified failed on "+this)
    }
    def &&(that : PAFormula) = PAConjunction(this::that::Nil).simplified
    def ||(that : PAFormula)  = PADisjunction(this::that::Nil).simplified
    // Get a stream of the DNF form of the formula
    def getEquations = getEquations_tailrec(Nil)

    def getEquations_tailrec(currentList: List[PAEquation]) : Stream[List[PAEquation]] = this match {
      case t@PADivides(_, _)     => Stream(currentList++List(t))
      case t@PAEqualZero(_)      => Stream(currentList++List(t))
      case t@PAGreaterZero(_)    => Stream(currentList++List(t))
      case t@PAGreaterEqZero(_)  => Stream(currentList++List(t))
      case PAConjunction(Nil)    => Stream(currentList)
      case PAConjunction(a::Nil)   => a.getEquations_tailrec(currentList)
      case PAConjunction(a::q)   => a.getEquations flatMap { eq => PAConjunction(q).getEquations_tailrec(currentList ++ eq) }
      case PADisjunction(Nil)    => Stream(List(PAFalse()))
      case PADisjunction(a::Nil) => a.getEquations_tailrec(currentList)
      case PADisjunction(a::q) => a.getEquations_tailrec(currentList) append PADisjunction(q).getEquations_tailrec(currentList)
      case PATrue() => Stream(List(PATrue()))
      case PAFalse() => Stream(List(PAFalse()))
      //case PANegation(f)
    }
  }
  
  // Atomic equations
  abstract sealed class PAEquation extends PAFormula {
    override def simplified: PAEquation = this match {
      case PADivides(1, pac) => PATrue()
      case PADivides(n, PACombination(i, Nil, Nil)) => if((i % n) == 0) PATrue() else PAFalse()
      case PADivides(0, pac) => PAEqualZero(pac).simplified
      case PADivides(n, pac) => PADivides(n, pac.simplified) // OptimizeMe !
      case PAEqualZero(pac) => PAEqualZero(pac.simplified.normalized) match {
        case PAEqualZero(PACombination(0, Nil, Nil)) => PATrue()
        case PAEqualZero(PACombination(n, Nil, Nil)) => PAFalse()
        case t => t
      }
      case PAGreaterZero(pac) => PAGreaterZero(pac.simplified.normalized) match {
        case PAGreaterZero(PACombination(n, Nil, Nil)) if n >  0 => PATrue()
        case PAGreaterZero(PACombination(n, Nil, Nil)) if n <= 0 => PAFalse()
        case t => t
      }
      case PAGreaterEqZero(pac) => PAGreaterEqZero(pac.simplified.normalized) match {
        case PAGreaterEqZero(PACombination(n, Nil, Nil)) if n >= 0 => PATrue()
        case PAGreaterEqZero(PACombination(n, Nil, Nil)) if n <  0 => PAFalse()
        case t => t
      }
      case PATrue() => PATrue()
      case PAFalse() => PAFalse()
    }
    def replace(y: PAVariable, t: PACombination): PAEquation
  }
  abstract class PATerm extends PAExpression {
    def replace(y: PAVariable, t: PACombination):PATerm
    def simplified:PATerm
    def replaceList(lxt : List[(PAVariable, PACombination)]): PATerm = {
      lxt.foldLeft(this){ case (result, (x, t)) => result.replace(x, t) }
    }

    def replaceList(lxt : List[(PAVariable, PACombination)], lyt : List[(PAVariable, PACombination)]): PATerm = {
      this.replaceList(lxt).replaceList(lyt)
    }
  }
  
  case class PADivision(numerator : PACombination, denominator : Int) extends PATerm {
    def replace(y: PAVariable, t: PACombination):PATerm = PADivision(numerator.replace(y, t), denominator).simplified

    def simplified:PATerm = (numerator.simplified, denominator) match {
      case (n, 1) => n
      case (n, 0) => PADivision(n, 0)
      case (PACombination(n, Nil, Nil), d) => PACombination((n - (d + (n % d))%d)/d, Nil, Nil)
      case (n, d) => PADivision(n, d)
    }
  }
  
  case class PAMinimum(expressions: List[PATerm]) extends PATerm {
    def replace(y: PAVariable, t: PACombination):PATerm = PAMinimum(expressions map (_.replace(y, t))).simplified
    def simplified:PATerm = expressions match {
      case Nil => PACombination(0, Nil, Nil)
      case a::Nil => a.simplified
      case a::b::q =>
        (a.simplified, b.simplified) match {
          case (PACombination(i, Nil, Nil), PACombination(j, Nil, Nil)) => PAMinimum(PACombination(Math.min(i, j), Nil, Nil)::q).simplified //OptimizeMe
          case (a, b) => PAMinimum(a::b::(q map (_.simplified)))
        }
    }
  }
  case class PAMaximum(expressions: List[PATerm]) extends PATerm {
    def replace(y: PAVariable, t: PACombination):PATerm = PAMaximum(expressions map (_.replace(y, t))).simplified
    def simplified:PATerm = expressions match {
      case Nil => PACombination(0, Nil, Nil)
      case a::Nil => a.simplified
      case a::b::q =>
        (a.simplified, b.simplified) match {
          case (PACombination(i, Nil, Nil), PACombination(j, Nil, Nil)) => PAMaximum(PACombination(Math.max(i, j), Nil, Nil)::q).simplified //OptimizeMe
          case (a, b) => PAMaximum(a::b::(q map (_.simplified)))
        }
    }
  }
  
  object PACombination {
    def apply(v: PAVariable):PACombination = this(1, v)
    def apply(k: Int, v: PAVariable):PACombination=  v match {
      case v@InputVar(n) => PACombination(0, (k, v)::Nil, Nil)
      case v@OutputVar(n) => PACombination(0, Nil, (k, v)::Nil)
    }
    def apply(i: Int): PACombination = PACombination(i, Nil, Nil)
  }

  case class PACombination(coefficient: Int, input_affine: List[(Int, InputVar)], output_affine: List[(Int, OutputVar)]) extends PATerm {
    // Sorting functions
    def by_InputVar_name(i1:(Int, InputVar), i2:(Int, InputVar)) : Boolean = (i1, i2) match {
      case ((_, InputVar(name1)), (_, InputVar(name2))) => name1 < name2
    }
    def by_OutputVar_name(i1:(Int, OutputVar), i2:(Int, OutputVar)) : Boolean = (i1, i2) match {
      case ((_, OutputVar(name1)), (_, OutputVar(name2))) => name1 < name2
    }
    // Regrouping functions
    def fold_Inputvar_name(i:(Int, InputVar), regrouped_vars:List[(Int, InputVar)]):List[(Int, InputVar)] = (i, regrouped_vars) match {
      case (i, Nil) => i::Nil
      case ((coef1, InputVar(name1)), (coef2, InputVar(name2))::q) if name1 == name2 => (coef1 + coef2, InputVar(name1))::q
      case (i, q) => i::q 
    }
    def fold_Outputvar_name(i:(Int, OutputVar), regrouped_vars:List[(Int, OutputVar)]):List[(Int, OutputVar)] = (i, regrouped_vars) match {
      case (i, Nil) => i::Nil
      case ((coef1, OutputVar(name1)), (coef2, OutputVar(name2))::q) if name1 == name2 => (coef1 + coef2, OutputVar(name1))::q
      case (i, q) => i::q
    }
    
    /// Simplified means that the variables are alphabetically sorted, that there are no null coefficients, and the gcd of all coefficients is 1.
    def simplified: PACombination = {
      val input_affine2  = (input_affine  sort by_InputVar_name ).foldRight[List[(Int, InputVar)]](Nil){ case (a, b) => fold_Inputvar_name(a, b)}
      val output_affine2 = (output_affine sort by_OutputVar_name).foldRight[List[(Int, OutputVar)]](Nil){ case (a, b) => fold_Outputvar_name(a, b)}
      PACombination(coefficient, input_affine2 remove (_._1 == 0), output_affine2 remove (_._1 == 0))
    }
    def normalized: PACombination = {
      val gcd = Common.gcdlist(coefficient :: ((input_affine map (_._1)) ++ (output_affine map (_._1))))
      PACombination(coefficient, input_affine, output_affine)/gcd
    }
    
    /// Division of this combination by an integer
    def /(i : Int): PACombination = {
      PACombination(coefficient / i, input_affine map {t => (t._1 / i, t._2)}, output_affine map {t => (t._1 / i, t._2)})
    }
    /// Multiplication by an integer
    def *(i : Int): PACombination = {
      PACombination(coefficient * i, input_affine map {t => (t._1 * i, t._2)}, output_affine map {t => (t._1 * i, t._2)})
    }
    /// Addition between two combinations
    def +(pac : PACombination): PACombination = pac match {
      case PACombination(c, i, o) => 
        PACombination(coefficient + c, input_affine ++ i, output_affine ++ o).simplified
    }
    /// Substraction between two combinations
    def -(that : PACombination): PACombination = this + (that * (-1))
    /// Addition with a new variable and its coefficient
    def +(kv : (Int, OutputVar)): PACombination = this + PACombination(0, Nil, kv::Nil)
    def +(k : Int): PACombination = this + PACombination(k, Nil, Nil)
    /// Substraction with a new variable and its coefficient
    def -(kv : (Int, OutputVar)): PACombination = this - PACombination(0, Nil, kv::Nil)
    def -(k : Int): PACombination = this + PACombination(-k, Nil, Nil)
    def unary_-(): PACombination = PACombination(0, Nil, Nil) - this
    /// Comparison
    def ===(that: PACombination) = PAEqualZero(this - that)
    def >= (that: PACombination) = PAGreaterEqZero(this - that)
    def >  (that: PACombination) = PAGreaterZero(this - that)
    def <= (that: PACombination) = PAGreaterEqZero((-this) + that)
    def <  (that: PACombination) = PAGreaterZero((-this) + that)
    
    /// Replacement of a variable by another
    def replace(y: PAVariable, t: PACombination):PACombination = (y, t) match {
      case (OutputVar(name), pac_for_y@PACombination(c2, i2, o2)) => 
        val (output_affine_with_y, output_affine_without_y) = output_affine partition (_._2 == y)
        val pac_without_y = PACombination(coefficient, input_affine, output_affine_without_y)
        val total_y_coefficient = (output_affine_with_y map (_._1)).foldLeft(0)(_+_)
        val result = pac_without_y + (pac_for_y*total_y_coefficient)
        result.simplified
      case (InputVar(name), pac_for_y@PACombination(c2, i2, o2)) => 
        val (input_affine_with_y, input_affine_without_y) = input_affine partition (_._2 == y)
        val pac_without_y = PACombination(coefficient, input_affine_without_y, output_affine)
        val total_y_coefficient = (input_affine_with_y map (_._1)).foldLeft(0)(_+_)
        val result = pac_without_y + (pac_for_y*total_y_coefficient)
        result.simplified
    }
    
    def %%(m: Int):PACombination = PACombination(Common.smod(coefficient, m),
                                                 input_affine  map { case (k, iv) => (Common.smod(k, m), iv)},
                                                 output_affine map { case (k, ov) => (Common.smod(k, m), ov)}).simplified
    
    def toNiceString:String = {
      def inputElementToString(kv : (Int, InputVar)) = kv._1 match {
        case 1 => kv._2.name
        case -1 => "-" + kv._2.name
        case k => k + "*" + kv._2.name
      }
      def outputElementToString(kv : (Int, OutputVar)) = kv._1 match {
        case 1 => kv._2.name
        case -1 => "-" + kv._2.name
        case k => k + "*" + kv._2.name
      }
      def makePlus(l: List[String]):String = l match {
        case Nil => ""
        case a::p => val s = makePlus(p)
        if(s=="") a
        else if(a=="") s
        else if(s.charAt(0) == '-')
          a + s
        else
          a + "+" + s
      }
      var c_string = if(coefficient == 0) "" else coefficient.toString
      var i_string = input_affine match {
        case Nil => ""
        case a::l => l.foldLeft(inputElementToString(a)) { (s, t2) =>
          val t2s = inputElementToString(t2)
          s + (if(t2s.charAt(0) =='-') t2s else "+" + t2s)}
      }
      var o_string = output_affine match {
        case Nil => ""
        case a::l => l.foldLeft(outputElementToString(a)) { (s, t2) =>
          val t2s = outputElementToString(t2)
          s + (if(t2s.charAt(0) =='-') t2s else "+" + t2s)}
      }
      val s = makePlus(c_string::i_string::o_string::Nil)
      if(s == "") "0" else s
    }
  }
  
  case class PADivides (coefficient: Int, pac: PACombination) extends PAEquation {
    override def replace(y: PAVariable, t: PACombination): PAEquation = PADivides(coefficient, pac.replace(y, t)).simplified
  }
  case class PAEqualZero    (pac: PACombination) extends PAEquation {
    override def replace(y: PAVariable, t: PACombination): PAEquation = PAEqualZero(pac.replace(y, t)).simplified
  }
  case class PAGreaterZero  (pac: PACombination) extends PAEquation {
    override def replace(y: PAVariable, t: PACombination): PAEquation = PAGreaterZero(pac.replace(y, t)).simplified
  }
  case class PAGreaterEqZero(pac: PACombination) extends PAEquation {
    override def replace(y: PAVariable, t: PACombination): PAEquation = PAGreaterEqZero(pac.replace(y, t)).simplified
  }
  case class PATrue() extends PAEquation {
    override def replace(y: PAVariable, t: PACombination): PAEquation = PATrue()
  }
  case class PAFalse() extends PAEquation {
    override def replace(y: PAVariable, t: PACombination): PAEquation = PAFalse()
  }
  
  case class PAConjunction(eqs : List[PAFormula]) extends PAFormula {
    
    override def replace(y: PAVariable, t: PACombination): PAFormula = PAConjunction(eqs map (_.replace(y, t))).simplified
  }
  case class PADisjunction(eqs : List[PAFormula]) extends PAFormula {

    override def replace(y: PAVariable, t: PACombination): PAFormula = PADisjunction(eqs map (_.replace(y, t))).simplified
  }
  //Combines the two sentences, adding a "\n" if needed
  def combineSentences(s1: String, s2: String):String = (if(s1.endsWith("\n") || s1 == "") s1 else s1 + "\n") + s2
  
  def inputAssignmentToScalaString(t: (InputVar, PATerm)) = t match {
    case (i, t) => "val "+ i.name + " = " + t
  }
  
  //Combines input sentences
  def innerScalaInput(input_assignment:List[(InputVar, PATerm)], indent:String):String = {
    val prog_input = input_assignment map {case assignment => indent + inputAssignmentToScalaString(assignment)} match {
      case Nil => ""
      case l => l reduceLeft {(t1, t2) => (t1 + "\n" + t2)}
    }
    prog_input
  }

  abstract class PAAbstractProgram
  
  object PACaseSplit {
    def empty:PACaseSplit = PACaseSplit(Nil)
    def toScalaString(indent: String, programs: List[(PACondition, PAProgram)]) = {
      val indent2 = indent + "  "
      (programs match {
        case Nil => ""
        case ((cond, pap)::Nil) =>
          pap.innerScalaContent(indent)
        case ((cond, pap)::_::q) =>
          indent + "val "+pap.resultScalaContent("")+" = "+
          (programs map {
            case (cond, pap) =>
              val prog_if = "if("+(cond.conditionToScalaString)+") {"
              val prog_ifthen = pap.innerScalaContent(indent2)
              val prog_ifthenresult = pap.resultScalaContent(indent2)
              val prog_ifend = indent + "}"
              (prog_if::prog_ifthen::prog_ifthenresult::prog_ifend::Nil).reduceLeft(combineSentences(_, _))
          }).reduceLeft( _ + " else " + _)
      })
    }
  }
  
  case class PACaseSplit(programs: List[(PACondition, PAProgram)]) extends PAAbstractProgram {
    override def toString = toScalaString("  ")
    def toScalaString(indent: String) = PACaseSplit.toScalaString("  ", programs)
    def execute(l: Map[InputVar, Int]): Map[OutputVar, Int] = {
      programs foreach {
        case (cond, prog) =>
          if(cond.execute(l)) return prog.execute(l)
      }
      Map[OutputVar, Int]()
    }
  }
  
  // Programs
  object PAProgram {
    def empty:PAProgram = PAProgram(Nil, Nil, PACaseSplit.empty, Nil, Nil)
    def optimized(input_variables: List[InputVar],
                  input_assignment: List[(InputVar, PATerm)],
                  case_splits: PACaseSplit,
                  output_assignment: List[(OutputVar, PATerm)],
                  output_variables: List[OutputVar]):PAProgram = {
      val final_output_variables = output_variables
      
      // Let's filter all assignments which are not useful (like for example the ones resulting from divisibility conditions)
      /*val (useful_output_assignments, _) = output_assignment.foldRight((Nil:List[(OutputVar, PATerm)], final_output_variables:List[OutputVar])) {
        case (assignment@(x, t), (useful_output_assignments, useful_output_variables)) =>
          if(useful_output_variables contains x) { // Then it's useful
            (assignment::useful_output_assignments, t.output_variables ++ useful_output_variables)
          } else { // Then this variable is useless 
            (useful_output_assignments, useful_output_variables)
          }
      }*/
      // Let's propagate assignments that are temporary
      val (reduced_input_assignments, reduced_output_assignments) = propagation_delete_temp(input_assignment, output_assignment, Nil, Nil, output_variables)
      PAProgram(input_variables, reduced_input_assignments, case_splits, reduced_output_assignments, output_variables)
    }
    def merge_disjunction(input_variables : List[InputVar],
                          output_variables: List[OutputVar],
                          programs_conditions: List[(PACondition, PAProgram)]): (PACondition, PAProgram) = {
      //Adds the global precondition the disjunction fo the case split conditions.
      val programs_conditions_filtered = programs_conditions remove (_._1.global_condition == PAFalse())
      programs_conditions_filtered find (_._1.global_condition == PATrue()) match {
        case Some(complete_program) => complete_program
        case None =>
          programs_conditions_filtered match {
            case Nil => (PACondition.empty, PAProgram.empty)
            case a::Nil => a
            case _ => 
              val splitted_conditions:List[PACondition] = programs_conditions_filtered map (_._1)
              val splitted_formulas:List[PAFormula] = splitted_conditions map (_.global_condition)
              val global_precondition = PADisjunction(splitted_formulas).simplified
              (PACondition.optimized(Nil, global_precondition),
               PAProgram(input_variables, Nil, PACaseSplit(programs_conditions_filtered), Nil, output_variables))
          }
      }
    }
  }
  def toPAInputAssignment(imap : Map[InputVar, Int]):List[(InputVar, PACombination)] =
    imap.toList map {case (v, i) => (v, PACombination(i, Nil, Nil))}
  def toPAOutputAssignment(imap : Map[OutputVar, Int]):List[(OutputVar, PACombination)] =
    imap.toList map {case (v, i) => (v, PACombination(i, Nil, Nil))}
  
  case class PAProgram(input_variables: List[InputVar],
                       input_assignment: List[(InputVar, PATerm)],
                       case_splits: PACaseSplit,
                       output_assignment: List[(OutputVar, PATerm)],
                       output_variables: List[OutputVar]) extends PAAbstractProgram {
    var name="result"
    def setName(new_name: String) = name = new_name
    
    override def toString = toScalaString("  ")
    
    def innerScalaContent(indent:String):String = {
      val prog_input = innerScalaInput(input_assignment, indent)
      val prog_case_split = case_splits.toScalaString(indent)
      val prog_output = output_assignment map {case (i, t) => indent+"val "+ i.name + " = " + t} match {
        case Nil => ""
        case l => l reduceLeft (combineSentences(_, _))
      }
      (prog_input::prog_case_split::prog_output::Nil).reduceLeft(combineSentences(_, _))
    }
    
    def resultScalaContent(indent:String):String = {
      indent+(output_variables match {
        case Nil => ()
        case (a::Nil) => a.name
        case l => "(" + (l map (_.name) sort {_ < _} reduceLeft (_+", "+_)) + ")"
      })
    }
    
    def inputScalaContent:String = input_variables match {
      case Nil => ""
      case l => (input_variables map (_.name + " : Int") reduceLeft (_+", "+_))
    }
    
    def toScalaString(indent: String):String = {
      val return_type = output_variables match {
        case Nil => "()"
        case (a::Nil) => "Int"
        case l => "("+(l map {_=>"Int"} reduceLeft (_ + ", " + _)) +")"
      }
      val function_definition = "def "+name+"("+inputScalaContent+"):" + return_type + " = {"
      val inner_content= innerScalaContent(indent)
      val result = resultScalaContent(indent)
      var prog = function_definition
      (function_definition::inner_content::result::"}"::Nil).reduceLeft(combineSentences(_, _))
    }
    
    // Exectues the program on a list of arguments, return the values of the outputvars.
    def execute(l: Map[InputVar, Int]): Map[OutputVar, Int] = {
      var input_value_map = l
      input_assignment foreach {
        case (v, t) => t.replaceList(toPAInputAssignment(input_value_map)) match {
          case PACombination(i, Nil, Nil) => input_value_map += (v -> i) 
          case _ => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
        }
      }
      var output_value_map = case_splits.execute(input_value_map)
      val input_assignments_listed = toPAInputAssignment(input_value_map)
      output_assignment foreach {
        case (v, t) =>
          t.replaceList(input_assignments_listed, toPAOutputAssignment(output_value_map)) match {
          case PACombination(i, Nil, Nil) => output_value_map += (v -> i) 
          case _ => throw new Exception("Was not able to reduce term "+t+" to integer under the mappings "+input_value_map+" and "+output_value_map)
        }
      }
      Map[OutputVar, Int]() ++ (output_variables map {case v => (v, (output_value_map(v)))})
    }
  }
  
  // Filters the useful assignments from the one that are useless.
  object PACondition {
    def empty: PACondition = PACondition(Nil, PAFalse())
    def optimized(input_assignment: List[(InputVar, PATerm)], global_condition: PAFormula):PACondition = {
      val final_input_variables = (global_condition.input_variables).removeDuplicates
      
      val (useful_input_assignments, _) = input_assignment.foldRight((Nil:List[(InputVar, PATerm)], final_input_variables:List[InputVar])) {
        case (assignment@(x, t), (useful_input_assignments, useful_input_variables)) =>
          if(useful_input_variables contains x) { // Then it's useful
            (assignment::useful_input_assignments, t.input_variables ++ useful_input_variables)
          } else { // Then this variable is useless 
            (useful_input_assignments, useful_input_variables)
          }
      }
      PACondition(useful_input_assignments, global_condition.simplified)
    }
  }
  
  case class PACondition(input_assignment: List[(InputVar, PATerm)], global_condition: PAFormula) {
    def conditionToScalaString = input_assignment match {
      case Nil => global_condition.toString
      case _ => "{"+(input_assignment map (inputAssignmentToScalaString(_)) reduceLeft (_+";"+_)) + ";"+global_condition.toString+"}"
    }
    
    override def toString = conditionToScalaString
    
    def execute(l: Map[InputVar, Int]): Boolean = {
      var input_value_map = l
      input_assignment foreach {
        case (v, t) => t.replaceList(toPAInputAssignment(input_value_map)) match {
          case PACombination(i, Nil, Nil) => input_value_map += (v -> i) 
          case _ => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
        }
      }
      global_condition.replaceList(toPAInputAssignment(input_value_map)) match {
        case PATrue() => true
        case PAFalse() => false
        case t => throw new Exception ("Could not find the truth value of "+this+" under the mapping "+input_value_map+". Got the result: "+t)  
      }
    }
  }
  
  /// Other definitions
    
  // ************* Different ways of specifying solving conditions ***************///
  
  def getOutputVariables(eqs: List[PAEquation]):List[OutputVar] = {
    (eqs flatMap (_.output_variables)).removeDuplicates
  }
  
  def solveEquations(name: String, variables: List[OutputVar], eqs: List[PAEquation]) = {
    var (cond, prog) = (new PASynthesis(eqs, variables)).solve()
    prog.setName(name)
    (cond, prog)
  }
  
  def solve(name: String, variables: List[OutputVar], formula_sequence: PAFormula*):(PACondition, PAProgram) = {
    val formula = PAConjunction(formula_sequence.toList).simplified
    val dnf:Stream[List[PAEquation]] = formula.getEquations
    val output_variables = variables
    val input_variables = formula.input_variables
    val programs_conditions = (dnf map {solveEquations("", output_variables, _)}).toList
    var (cond, prog) = PAProgram.merge_disjunction(input_variables, output_variables, programs_conditions)
    prog.setName(name)
    (cond, prog)
  }
  def solve(name: String, formula_sequence: PAFormula*):(PACondition, PAProgram) = {
    solve(name, formula_sequence.toList)
  }
  def solve(name: String, formula_sequence: List[PAFormula]):(PACondition, PAProgram) = {
    val formula = PAConjunction(formula_sequence.toList).simplified
    solve(name, formula.output_variables, formula)
  }
  def solve(variables:List[OutputVar], formula_sequence: PAFormula*):(PACondition, PAProgram) = {
    solve(variables, formula_sequence.toList)
  }
  def solve(variables:List[OutputVar], formula_sequence: List[PAFormula]):(PACondition, PAProgram) = {
    val formula = PAConjunction(formula_sequence.toList).simplified
    solve("result", variables, formula)
  }
  def solve(formula_sequence: PAFormula*):(PACondition, PAProgram) = {
    solve(formula_sequence.toList)
  }
  def solve(formula_sequence: List[PAFormula]):(PACondition, PAProgram) = {
    val formula = PAConjunction(formula_sequence).simplified
    solve("result", formula.output_variables, formula)
  }
  

  /// ************* Function used in the algorithm ***************///
  val alphabet = "abcdefghijklmnopqrstuvwxyz"
  def newOutputVariable(input_existing: List[InputVar], output_existing : List[OutputVar]): OutputVar = {
    //var typical = "xyzmnpqrstuvw"
    var i = 0
    val names = (input_existing map (_.name)) ++ (output_existing map (_.name))
    (0 to 25) foreach { i =>
      val test = "y"+alphabet.substring(i, i+1)
      if(!(names contains test))
        return OutputVar(test)
    }
    while(names contains ("y"+i)) {
      i+=1
    }
    OutputVar("y"+i)
  }
  var tested_input_variables:List[InputVar] = Nil
  def newInputVariable(input_existing: List[InputVar], output_existing : List[OutputVar]): InputVar = {
    var i = 0
    val names = (input_existing map (_.name)) ++ (output_existing map (_.name)) ++ (tested_input_variables map (_.name))
    while(names contains ("x"+i)) {
      i += 1
    }
    val result = InputVar("x"+i)
    tested_input_variables = result::tested_input_variables
    result
  }
  
  // Split the list into PAEqualZero one left and not PAEqualZero on right
  def partitionPAEqualZero(eqs : List[PAEquation]):(List[PAEqualZero], List[PAEquation]) = eqs match {
    case Nil => (Nil, Nil)
    case (p@PAEqualZero(pac)::q) =>
      val (a, b) = partitionPAEqualZero(q)
      (PAEqualZero(pac)::a, b)
    case (p::q) =>
      val (a, b) = partitionPAEqualZero(q)
      (a, p::b)
  }
  // Splits the list into equalities, inequalities, and a boolean indicating if the system is consistent.
  def partitionPAGreaterEqZero(eqs : List[PAEquation]):(List[PAEqualZero], List[PAGreaterEqZero], Boolean) = eqs match {
    case Nil => (Nil, Nil, true)
    case (p@PAEqualZero(pac)::q) =>
      val (a, b, c) = partitionPAGreaterEqZero(q)
      (PAEqualZero(pac)::a, b, c)
    case (p@PAGreaterEqZero(pac)::q) =>
      val (a, b, c) = partitionPAGreaterEqZero(q)
      (a, PAGreaterEqZero(pac)::b, c)
    case (p@PAGreaterZero(PACombination(coef, i, o))::q) =>
      val (a, b, c) = partitionPAGreaterEqZero(q)
      (a, PAGreaterEqZero(PACombination(coef-1, i, o))::b, c)
    case (PATrue()::q) =>
      partitionPAGreaterEqZero(q)
    case (PAFalse()::q) =>
      (Nil, Nil, false)
    case (k::q) => throw new Exception(k + " is not supported at this point. Shoujld have been converted earlier.")
  }

  
  def recursive_propagation(
      output_assignments : List[(OutputVar, PATerm)],
      assignments_to_propagate : List[(OutputVar, PACombination)],
      interesting_variables : List[OutputVar])
        : List[(OutputVar, PATerm)]  =
      output_assignments match {
    case Nil => Nil
    case (v, pac@PACombination(_, _, _))::q => pac.replaceList(assignments_to_propagate) match {
      case pac@PACombination(_, Nil, Nil) => // We propagate constants
        if(interesting_variables contains v) {
          (v, pac)::recursive_propagation(q, (v,pac)::assignments_to_propagate, interesting_variables)
        } else {
          recursive_propagation(q, (v,pac)::assignments_to_propagate, interesting_variables)
        }
      case t => (v, t)::recursive_propagation(q, assignments_to_propagate, interesting_variables)
    }
    case (v, t)::q => (v, t.replaceList(assignments_to_propagate))::recursive_propagation(q, assignments_to_propagate, interesting_variables)
  }
  
  def propagation_delete_temp(
      input_assignments : List[(InputVar, PATerm)],
      output_assignments : List[(OutputVar, PATerm)],
      assignments_to_propagate_input : List[(InputVar, PACombination)],
      assignments_to_propagate_output : List[(OutputVar, PACombination)],
      interesting_variables : List[OutputVar])
        : (List[(InputVar, PATerm)], List[(OutputVar, PATerm)]) = 
    recursive_propagation_delete_temp(input_assignments,
                                      output_assignments,
                                      assignments_to_propagate_input,
                                      assignments_to_propagate_output,
                                      interesting_variables, Nil, Nil)

  def recursive_propagation_delete_temp(
      input_assignments : List[(InputVar, PATerm)],
      output_assignments : List[(OutputVar, PATerm)],
      assignments_to_propagate_input : List[(InputVar, PACombination)],
      assignments_to_propagate_output : List[(OutputVar, PACombination)],
      interesting_variables : List[OutputVar],
      input_assignments_new : List[(InputVar, PATerm)],
      output_assignments_new : List[(OutputVar, PATerm)]
  )
        : (List[(InputVar, PATerm)], List[(OutputVar, PATerm)]) = {
      // First: input assignments and then output assignments
      input_assignments match {
        case Nil => 
          output_assignments match {
            case Nil => (input_assignments_new.reverse, output_assignments_new.reverse)
            case (v, t)::q => 
              t.replaceList(assignments_to_propagate_input, assignments_to_propagate_output) match {
              case t@PACombination(_, _, _) =>
                if(interesting_variables contains v) { // yes ! let's keep this variable
                  recursive_propagation_delete_temp(Nil, q,
                                                    assignments_to_propagate_input,
                                                    assignments_to_propagate_output ++ ((v,t)::Nil),
                                                    interesting_variables,
                                                    input_assignments_new,
                                                    (v, t)::output_assignments_new)
                } else { // Not interesting to keep this variable. Just replace its content.
                  recursive_propagation_delete_temp(Nil, q,
                                                    assignments_to_propagate_input,
                                                    assignments_to_propagate_output ++ ((v,t)::Nil),
                                                    interesting_variables,
                                                    input_assignments_new, output_assignments_new)
                }
              // The term is not affine, so we keep it without replacing.
              case t => recursive_propagation_delete_temp(Nil, q,
                                                          assignments_to_propagate_input,
                                                          assignments_to_propagate_output,
                                                          interesting_variables,
                                                          input_assignments_new,
                                                          (v, t)::output_assignments_new)
            }
          }
        // On input_assignments : they can be useful if case disjunctions, so we always keep them.
        // OptimizeMe : If not used in case disjunction, remove input variables.
        case (v, pac@PACombination(_, _, _))::q =>
          pac.replaceList(assignments_to_propagate_input, assignments_to_propagate_output) match {
            case t@PACombination(_, _, _) => // We propagate everything
              recursive_propagation_delete_temp(q, output_assignments,
                                                assignments_to_propagate_input ++ ((v,t)::Nil),
                                                assignments_to_propagate_output,
                                                interesting_variables,
                                                (v, t)::input_assignments_new,
                                                output_assignments_new)
            // The variable
            case t =>  recursive_propagation_delete_temp(q, output_assignments,
                                                assignments_to_propagate_input,
                                                assignments_to_propagate_output,
                                                interesting_variables,
                                                (v, t)::input_assignments_new,
                                                output_assignments_new)
          }
        case (v, t)::q =>
          recursive_propagation_delete_temp(q, output_assignments,
                                            assignments_to_propagate_input,
                                            assignments_to_propagate_output,
                                            interesting_variables,
                                            (v, t.replaceList(assignments_to_propagate_input, assignments_to_propagate_output))::input_assignments_new,
                                            output_assignments_new)
      }
      
    }
  
  // Propagate simple assignments, by removing the introduced variables if possible.
  def propagateAssignment(y: OutputVar, t: PACombination, output_assignments : List[(OutputVar, PATerm)], output_variables_initial : List[OutputVar]): List[(OutputVar, PATerm)]  = {
    recursive_propagation(output_assignments, (y,t)::Nil, output_variables_initial)
  }
}
// TODO : verify that the output_variable initial are the good ones by recursivity
class PASynthesis(equations: List[PASynthesis.PAEquation], output_variables_initial:List[PASynthesis.OutputVar]) {
  import PASynthesis._
  var output_variables:List[OutputVar] = output_variables_initial
  var output_variables_encountered:List[OutputVar]  = output_variables_initial
  
  val input_variables_initial:List[InputVar]  = (equations flatMap (_.input_variables)).removeDuplicates
  var input_variables:List[InputVar]  = input_variables_initial
  var input_variables_encountered:List[InputVar]  = input_variables_initial
  
  // Global_precondition is a conjunction of disjunctions of conjunctions.
  var global_precondition: List[PAFormula] = Nil
  // equation should not have output variables
  def addPrecondition (e: PAFormula)    = e.simplified match {
    case PATrue() => 
    case PAFalse() => setFalsePrecondition()
    case f => global_precondition = e :: global_precondition
  }
  def setFalsePrecondition() = global_precondition = PAFalse()::Nil
  def addOutputVar(y: OutputVar) = {
    output_variables = (y::output_variables)
    output_variables_encountered = (y::output_variables_encountered). removeDuplicates
  }
  def delOutputVar(y: OutputVar) = output_variables -= y
  def addInputVar (y: InputVar)  = {
    input_variables = (y::input_variables)
    input_variables_encountered = (y::input_variables_encountered)
  }
  def getNewOutputVarWithoutRegistering() = PASynthesis.newOutputVariable(input_variables_encountered, output_variables_encountered)
  def getNewOutputVar() = {
    val y = getNewOutputVarWithoutRegistering()
    addOutputVar(y)
    y
  }
  def getNewInputVar() = {
    val x = PASynthesis.newInputVariable(input_variables_encountered, output_variables_encountered)
    addInputVar(x)
    x
  }
  // List of reversed assignments: At the end, leftmost assignments should be done at the end.
  var input_assignments: List[(InputVar, PATerm)] = Nil
  var output_assignments: List[(OutputVar, PATerm)] = Nil
  def addInputAssignment (x: InputVar,  t: PATerm) = input_assignments  = input_assignments ++ ((x, t.simplified)::Nil)
  def addOutputAssignment(y: OutputVar, t: PATerm) = output_assignments = (y, t.simplified)::output_assignments

  ///*********** Functions used in the algorithm ***************//
  def simplifyEquations(equations: List[PASynthesis.PAEquation]) : List[PASynthesis.PAEquation] = {
    equations flatMap {
      case e@PASynthesis.PADivides(k, PASynthesis.PACombination(c, i, Nil)) =>
        addPrecondition(e.simplified)
        Nil
      case PADivides(k, PACombination(c, i, o)) =>
        val y = getNewOutputVar()
        PAEqualZero(PACombination(c, i, (k, y)::o)).simplified::Nil
      case PAGreaterZero(PACombination(c, i, o)) => PAGreaterEqZero(PACombination(c-1, i, o)).simplified::Nil
      case e => e.simplified::Nil
    }
  }
  /// Returns the remaining non_equalities (non_equalities should not contain equalities, nor will the returned term do)
  def solveEqualities(equalities : List[PAEqualZero], non_equalities : List[PAEquation]): List[PAEquation] = {
    /// Make sure all equalities have at least one output variable, else remove them.
    val (interesting_equalities, precondition_equalities) = equalities partition (_.has_output_variables)
    addPrecondition(PAConjunction(precondition_equalities))
    
    /// Sorting function (OptimizeMe)
    def by_least_outputvar_coef(eq1: PAEqualZero, eq2: PAEqualZero): Boolean = (eq1, eq2) match {
      case (PAEqualZero(pac1@PACombination(c1, i1, o1)), PAEqualZero(pac2@PACombination(c2, i2, o2))) =>
        val min_coefs_o1 = o1 map (_._1) map Math.abs reduceLeft (Math.min(_, _))
        val min_coefs_o2 = o2 map (_._1) map Math.abs reduceLeft (Math.min(_, _))
        min_coefs_o1 < min_coefs_o2
    }
    
    val sorted_equalities = interesting_equalities sort by_least_outputvar_coef
    
    sorted_equalities match {
      case Nil => non_equalities
      case (eq1@PAEqualZero(PACombination(c1, i1, o1)))::rest_equalities =>
        val o1_coefs = o1 map (_._1)
        val o1_vars = o1 map (_._2)
        Common.gcdlist(o1_coefs) match {
          case 1 => 
            // We find a solution to o1_coefs.o1_vars + 1 = 0
            // Then we know that by multiplying the first line by coef+i1_coef.i1.vars, we obtain the general solution
            val pa_input = PACombination(c1, i1, Nil)
            val solution_for_1 = Common.bezoutWithBase(1, o1_coefs)
            val first_line:List[PACombination] = solution_for_1.head map (pa_input * _)
            // From this solution, we introduce |o1| - 1 new variables to solve the equality and remove the equation.
            val new_assignments = solution_for_1.tail.foldLeft(first_line) { case (assignments, line) =>
                val y = getNewOutputVar()
                (assignments zip line) map { case (expr, coef) => expr + (y*coef)}
            }
            var new_equalities = rest_equalities
            var new_nonequalities = non_equalities
            (o1_vars zip new_assignments) foreach {
              case (v, pac) => addOutputAssignment(v, pac)
                val (new_eqs, blown_eqs) = partitionPAEqualZero(new_equalities map (_.replace(v, pac)))
                new_equalities = new_eqs
                new_nonequalities = blown_eqs ++ (new_nonequalities map (_.replace(v, pac)))
                delOutputVar(v)
            }
            solveEqualities(new_equalities, new_nonequalities)

          case n => // n > 1
            /// Introduce a new input variable.
            val x = getNewInputVar()
            addPrecondition(PADivides(n, PACombination(c1, i1, Nil)))
            addInputAssignment(x, PADivision(PACombination(c1, i1, Nil), n))
            PAEqualZero(PACombination(0, (n, x)::Nil, o1)).simplified match { // Should divide by n, as it was the gcd of all other variables.
              case new_eq@PAEqualZero(_) => solveEqualities(new_eq::rest_equalities, non_equalities)
              case _ => solveEqualities(rest_equalities, non_equalities) // Should NOT happen as there is at least one variable in PAEqualZero so it cannot be jugded as something else.
            }
        }
    }
  }
  
  def setRemainingVariablesToZero(output_variables : List[OutputVar]):Unit = output_variables match {
    case Nil =>
    case y::q =>
      output_variables_initial contains y match {
        case true => output_assignments = propagateAssignment(y, PACombination(0, Nil, Nil), output_assignments, output_variables_initial)
                     addOutputAssignment(y, PACombination(0, Nil, Nil))
                     delOutputVar(y)
                     setRemainingVariablesToZero(q)
        case false => output_assignments = propagateAssignment(y, PACombination(0, Nil, Nil), output_assignments, output_variables_initial)
                      delOutputVar(y)
                      setRemainingVariablesToZero(q)
      }
  }
  
  // Needs the equalities to be already simplified.
  // The boolean indicates if the system is consistent.
  def removeRedundancies(inequalities: List[PAGreaterEqZero]): (List[PAGreaterEqZero], List[PAEqualZero], Boolean) = {
    def less_inputvar_combination(l1 : List[(Int, InputVar)], l2 : List[(Int, InputVar)]): Boolean = (l1, l2) match {
      case (Nil, Nil) => false
      case (Nil, _) => true
      case (_, Nil) => false
      case ((k1, InputVar(name1))::p, (k2, InputVar(name2))::q) => k1 < k2 || (k1 == k2 && (name1 < name2 || (name1 == name2 && less_inputvar_combination(p,q)))) 
    }
    def less_outputvar_combination(l1 : List[(Int, OutputVar)], l2 : List[(Int, OutputVar)]): Boolean = (l1, l2) match {
      case (Nil, Nil) => false
      case (Nil, _) => true
      case (_, Nil) => false
      case ((k1, OutputVar(name1))::p, (k2, OutputVar(name2))::q) => k1 < k2 || (k1 == k2 && (name1 < name2 || (name1 == name2 && less_outputvar_combination(p,q)))) 
    }
    
    // OptimizeMe (too much simplifications)!
    def by_coef_list(p1:PAGreaterEqZero, p2:PAGreaterEqZero) : Boolean = (p1, p2) match {
      case (PAGreaterEqZero(pac1@PACombination(c1, i1, o1)), PAGreaterEqZero(pac2@PACombination(c2, i2, o2))) =>
        less_inputvar_combination(i1, i2) || (i1 == i2 && less_outputvar_combination(o1, o2))
    }
    val inequalities_sorted = inequalities sort by_coef_list
    inequalities_sorted.foldRight((Nil:List[PAGreaterEqZero], Nil:List[PAEqualZero], true))((_, _) match {
      case (p, (l1, l2, false)) => (l1, l2, false)
      case (p, (Nil, l, true)) => (p::Nil, l, true)
      case (p1@PAGreaterEqZero(pac1), ((p2@PAGreaterEqZero(pac2))::q, l, true)) if pac1.input_affine == pac2.input_affine && pac1.output_affine == pac2.output_affine =>
        if(pac1.coefficient > pac2.coefficient) {
          (p2::q, l, true)
        } else {
          (p1::q, l, true)
        }
      case (p1@PAGreaterEqZero(pac1), ((p2@PAGreaterEqZero(pac2))::q, l, true)) =>
        // p1 : K1+A1(x,y) >= 0
        // p2 : K2-A1(x,y) >= 0
        // so we should have pac1.coefficient = K1 >= -A1(x, y) >= -K2 = minus_pac2.coefficient in order to be solvable.
        // In case of equality, we can transform these two equations to an equality
        
        val minus_pac2 = pac2 * (-1)
        if(pac1.input_affine == minus_pac2.input_affine && pac1.output_affine == minus_pac2.output_affine) {
           if (pac1.coefficient < minus_pac2.coefficient) {
              // It's not compatible.
              (Nil, Nil, false)
           } else if(pac1.coefficient == minus_pac2.coefficient) {
              // It is like an equality
              (q, PAEqualZero(pac1)::l, true)
           } else {
             // They determine a region enclosed between two parallel lines, which is compatible.
             (p1::p2::q, l, true)
           }
        } else {
          // They are not related so compatible
          (p1::p2::q, l, true)
        }
      }
    )
  }
  
  // Returns (l_left, l_right, l_remaining) such that:
  // l_left contains elements  (A, a) such that A <= a*v
  // l_right contains elements (b, B) such that b*v <= B
  // l_remaining contains elements which do not contain v
  def getInequalitiesForVariable(v: OutputVar, inequalities:List[PAGreaterEqZero]): (List[(PACombination, Int)], List[(Int, PACombination)], List[PAGreaterEqZero]) = {
    def getInequalitiesForVariable_aux(v: OutputVar,
                                     inequalities:List[PAGreaterEqZero],
                                     result:(List[(PACombination, Int)], List[(Int, PACombination)], List[PAGreaterEqZero])
                                    )   :   (List[(PACombination, Int)], List[(Int, PACombination)], List[PAGreaterEqZero]) = inequalities match {
        case Nil => result
      case ((p@PAGreaterEqZero(pac@PACombination(c, i, o)))::q) => val (l_left, l_right, l_remaining)=result
        o find (_._2 == v) match {
          case None =>
              getInequalitiesForVariable_aux(v, q, (l_left, l_right, p::l_remaining))
          case Some(found_element@(k, v)) =>
            if(k > 0)
              getInequalitiesForVariable_aux(v, q, ((PACombination(c, i, o - found_element) * (-1), k)::l_left, l_right, l_remaining))
            else
              getInequalitiesForVariable_aux(v, q, (l_left, (-k, PACombination(c, i, o - found_element))::l_right, l_remaining))
        }
    }
    getInequalitiesForVariable_aux(v, inequalities, (Nil, Nil, Nil))
  }
  
  def solve():(PACondition, PAProgram) = {
    ///*********** Main algorithm ***************//
    //***** Step 1: There are no quantifiers by construction. Nothing to do
    //***** Step 2: Remove divisibility constraints
    // Convert "Greater" to "GreaterEq"
    // Simplify everything
    val equations2 = simplifyEquations(equations)
    
    //***** Step 3 : converting to DNF : Nothing to do, the argument is a conjunction
    //***** Step 4 : Case Splitting. Nothing to do.
    //***** Step 5 : Removing equalities
    
    // All equations without output vars go directly to the global precondition
    val (eq_with_outputvars, eq_without_outputvars) = equations2 partition (_.has_output_variables) 
    addPrecondition(PAConjunction(eq_without_outputvars))
    // Retrieve all equalities
    var (equalities, non_equalities) = partitionPAEqualZero(eq_with_outputvars)
    /// Solve them, so now we only have non-equalities
    /// The simplification of inequalities can generate new equalities, so we handle them.
    def solveEquations(equalities:List[PAEqualZero], non_equalities:List[PAEquation]):Option[PACaseSplit] = {
      val non_equalities2 = solveEqualities(equalities, non_equalities)
      /// Get only inequalities, plus maybe with "False" in other
      val (equalities2, inequalities, is_consistent) = partitionPAGreaterEqZero(non_equalities2)
      // equalities2 should be empty given that new_non_equalities cannot contain equalities
      assert(equalities2 == Nil)
      if(!is_consistent) return None
  
      /// Remove redundant inequalities, maybe generating equalities
      val (inequalities3, equalities3, is_consistent3) = removeRedundancies(inequalities)
      if(!is_consistent3) return None

      if(equalities3 != Nil)
        return solveEquations(equalities3, inequalities3)
      val inequalities4 = inequalities3
      
      var current_inequalities = inequalities4
      /// Solves for unbounded variables. The value of output_variable is going to change, but we just need the initial one.
      var current_inequalities_saved = PATrue()::current_inequalities
      while(current_inequalities != current_inequalities_saved) {
        current_inequalities_saved = current_inequalities
        output_variables foreach { y =>
          getInequalitiesForVariable(y, current_inequalities) match {
            case (l_left@Nil, l_right@Nil, l_remaining) =>
              setRemainingVariablesToZero(y::Nil)
            case (l_left@Nil, l_right@l, l_remaining) =>
              // Only bounded on the right by equations of style b*y <= pac, so we know that the integer upper bounds are pac/b
              val upper_bounds = l_right map { case (b , pac) => PADivision(pac, b).simplified }
              addOutputAssignment(y, PAMinimum(upper_bounds))
              delOutputVar(y)
              current_inequalities = l_remaining
            case (l_left@l, l_right@Nil, l_remaining) =>
              // Only bounded on the left by equations of style pac <= a*y, so we know that the integer upper bounds are (pac+a-1)/a
              val lower_bounds = l_left map { case (pac, a) => PADivision(pac + PACombination(a-1), a).simplified }
              addOutputAssignment(y, PAMaximum(lower_bounds))
              delOutputVar(y)
              current_inequalities = l_remaining
            case _ =>
          }
        }
      }
      if(output_variables == Nil) {
        addPrecondition(PAConjunction(current_inequalities))
        return Some(PACaseSplit.empty)
      }
      
      // Now at this point, all variables are bounded on both sides.
      // Let's find the one for which the LCM of its coefficients is the smallest.
      val output_variables_with_min_coefs = output_variables map {
        case y =>
          // Both l_left and r_right are not empty because of the previous computation
          val (l_left, l_right, l_remaining) = getInequalitiesForVariable(y, current_inequalities)
          val min_coef = Common.lcmlist((l_left map {t => Math.abs(t._2)}) ++ (l_right map {t => Math.abs(t._1)}))
          (min_coef, y)
      } 
      def min_coef(i1:(Int, OutputVar), i2:(Int, OutputVar)) : (Int, OutputVar) = (i1, i2) match {
        case (t1@(k1, v1), t2@(k2, v2)) => if(k1 < k2) t1 else t2 
      }
      val (_, y) = output_variables_with_min_coefs.reduceRight(min_coef(_, _))
      // Now y is the variable having the least coefficient among the variables.
      val (l_left, l_right, l_remaining) = getInequalitiesForVariable(y, current_inequalities) 
      current_inequalities = l_remaining

      //  Partial modulo ending feasability
      val partial_modulo_ending_feasible = l_left forall{ case (eqA, a) =>
        a == 1 || (
        l_right forall { case (b, eqB) =>
          b == 1 ||
            (((eqB*a) - (eqA*b)) match {
              case PACombination(k, Nil, Nil) if k >= a*b - Math.max(a, b) => true
              case _ => false
            })
        })
      }
      if(partial_modulo_ending_feasible) {
        if(l_right.size <= l_left.size) {
          val upper_bounds = l_right map { case (b , pac) => PADivision(pac, b).simplified } // Copy paste from above
          addOutputAssignment(y, PAMinimum(upper_bounds))
          delOutputVar(y)
        } else {
          val lower_bounds = l_left map { case (pac, a) => PADivision(pac + PACombination(a-1), a).simplified }
          addOutputAssignment(y, PAMaximum(lower_bounds))
          delOutputVar(y)
        }
        
        // eqA <= a*y  and b*y <= eqB
        l_left foreach { case (eqA, a) =>
          l_right foreach { case (b, eqB) =>
            if(a==1) {
              current_inequalities = (PAGreaterEqZero(eqB-(eqA*b)))::current_inequalities
            } else if(b==1) {
              current_inequalities = (PAGreaterEqZero((eqB*a)-eqA))::current_inequalities
            } else {
              // Third case, we know that the eqB*a-eqA*b is big enough so that we are sure to find a solution
              // So we can safely drop this equation
            }
          }
        }
        if(current_inequalities == Nil) {
          Some(PACaseSplit.empty)
        } else {
          solveEquations(Nil, current_inequalities)
        }
      } else {
        if(l_right.size <= l_left.size) {
          val upper_bounds = l_right map { case (b , pac) => PADivision(pac, b).simplified } // Copy paste from above
          addOutputAssignment(y, PAMinimum(upper_bounds))
          delOutputVar(y)
        } else {
          val lower_bounds = l_left map { case (pac, a) => PADivision(pac + PACombination(a-1), a).simplified }
          addOutputAssignment(y, PAMaximum(lower_bounds))
          delOutputVar(y)
        }
        // OptimizeMe : If a is smaller than b, use it instead of a.
        var output_variables_used = (output_variables_encountered).removeDuplicates
        var input_variables_used = (input_variables_encountered).removeDuplicates
        
        // We collect a list of list of disjoint possibilities
        val disjoint_possibilities:List[List[(PAGreaterEqZero, PAEqualZero)]] = l_left flatMap { case (eqA, a) =>
          l_right flatMap { case (b, eqB) =>
            if(a==1) {
              current_inequalities = (PAGreaterEqZero(eqB-(eqA*b)))::current_inequalities
              Nil
            } else if(b==1) {
              current_inequalities = (PAGreaterEqZero((eqB*a)-eqA))::current_inequalities
              Nil
            } else {
              // If b is the smallest : 
              // Solve : a *(eqB % b)<= eqB*a - eqA*b
              // by :    a*0 <= eqB*a - eqA*b && eqB = b*y0+0
              //         a*1 <= eqB*a - eqA*b && eqB = b*y0+1
              //         ...
              //         a*(b-1) <= eqB*a - eqA*b && eqB = b*y0+(b-1)
              val pac_ab = ((eqB*a) - (eqA*b))
              val y = getNewOutputVar() // One variable for each new type of equation. Not for this problem.
              output_variables_used = y::output_variables_used
              
              val eq_possibilities : List[(PAGreaterEqZero, PAEqualZero)] = (0 to (b-1)).toList map { k:Int =>
                val new_ineq = PAGreaterEqZero(pac_ab - PACombination(k*a))
                val new_eq   = PAEqualZero(eqB - PACombination(k, Nil, (b, y)::Nil))
                // We have to collect all equations and inequations before processing.
                (new_ineq, new_eq)
              }
              List(eq_possibilities)
              // Third case, we know that the eqB*a-eqA*b is big enough so that we are sure to find a solution
              // So we can safely drop this equation
            }
          }
        }
        
        if(output_variables == Nil) { // We return all equations as preconditions
          var more_preconditions:List[PAFormula] = Nil
          def store(remaining_possibilities: List[List[(PAGreaterEqZero, PAEqualZero)]], current_choice: List[PAEquation]):Unit = remaining_possibilities match {
            case Nil => more_preconditions = PAConjunction(current_choice)::more_preconditions
            case (Nil::rest) => Nil
            case (((new_ineq, new_eq)::pos1)::rest) =>
              store(rest, new_ineq::new_eq::current_choice)
              store(pos1::rest, current_choice)
          }
          store(disjoint_possibilities, current_inequalities)
          addPrecondition(PADisjunction(more_preconditions))
          Some(PACaseSplit.empty)
        } else {
          // Now we have to take exactly a possibility into each one of the list, solve it, and this gives the PASplitCase
          def choose(remaining_possibilities: List[List[(PAGreaterEqZero, PAEqualZero)]], current_choice: List[PAEquation]):List[(PACondition, PAProgram)] = remaining_possibilities match {
            case Nil => List(PASynthesis.solve(output_variables, current_choice))
            case (Nil::rest) => Nil
            case (((new_ineq, new_eq)::pos1)::rest) => choose(rest, new_ineq::new_eq::current_choice) ++ choose(pos1::rest, current_choice)
          }
          Some(PACaseSplit(choose(disjoint_possibilities, current_inequalities)))
        }
      }
    }
    
    val result = solveEquations(equalities, non_equalities)
    
    // Looking for variables bounded only on one side.
    result match {
      case None =>
        setFalsePrecondition()
        (PACondition.optimized(Nil, PAConjunction(global_precondition)), PAProgram.empty)
      case Some(pa_split@PACaseSplit(list_cond_prog)) =>
        if(list_cond_prog != Nil) {
          //Adds the global precondition the disjunction fo the case split conditions.
          val splitted_conditions:List[PACondition] = list_cond_prog map (_._1)
          val splitted_formulas:List[PAFormula] = splitted_conditions map (_.global_condition)
          var formulas:List[PAFormula] = Nil
          splitted_conditions foreach {
            case PACondition(assignments, formula) =>
              assignments foreach {
                case (iv, t) => addInputAssignment(iv, t)
              }
          }
          addPrecondition(PADisjunction(splitted_formulas))
        } else {
          setRemainingVariablesToZero(output_variables)
        }
        (PACondition.optimized(input_assignments, PAConjunction(global_precondition)), PAProgram.optimized(input_variables_initial, input_assignments, pa_split, output_assignments, output_variables_initial))
    }
  }
}

