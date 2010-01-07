package synthesis

sealed abstract class APAAbstractCondition {
  def toCommonString : String
  def execute(l: Map[InputVar, Int]): Boolean
  def input_variables: List[InputVar]
}

// Filters the useful assignments from the one that are useless.
object APACondition {
  def False: APACondition = APACondition(Nil, APAFalse(), APAEmptySplitCondition())
  def optimized(input_assignment: List[InputAssignment], global_condition: APAFormula, pf : APASplitCondition):APACondition = {
      
    val final_input_variables = (global_condition.input_variables ++ pf.input_variables).removeDuplicates
    
    val (useful_input_assignments, _) = input_assignment.foldRight((Nil:List[InputAssignment], final_input_variables:List[InputVar])) {
      case (assignment@SingleInputAssignment(x, t), (useful_input_assignments, useful_input_variables)) =>
        if(useful_input_variables contains x) { // Then it's useful
          (assignment::useful_input_assignments, t.input_variables ++ useful_input_variables)
        } else { // Then this variable is useless 
          (useful_input_assignments, useful_input_variables)
        }
      case (assignment@BezoutInputAssignment(xl, tl), (useful_input_assignments, useful_input_variables)) =>
        if(xl exists (useful_input_variables contains _)) { // Then it's useful
          (assignment::useful_input_assignments, (tl flatMap (_.input_variables)) ++ useful_input_variables)
        } else { // Then this variable is useless 
          (useful_input_assignments, useful_input_variables)
        }
    }
    if(global_condition == APAFalse()) return APACondition.False
    val result = if(pf.input_variables == Nil) {
      pf.execute(Map()) match {
        case false => APACondition.False
        case true => APACondition(useful_input_assignments, global_condition.simplified, APAEmptySplitCondition())
      }
    } else {
      global_condition.simplified match {
        case t@APAFalse() => APACondition(useful_input_assignments, t, APAEmptySplitCondition())
        case t => APACondition(useful_input_assignments, t, pf)
      }
    }
    result
  }
}

case class APACondition(input_assignment: List[InputAssignment], global_condition: APAFormula, pf : APASplitCondition) extends APAAbstractCondition {
  def &&(more_cond: APAFormula):APACondition = APACondition(input_assignment, global_condition && more_cond, pf)
  def assumeBefore(more_cond: APAFormula):APACondition = APACondition(input_assignment, more_cond && global_condition, pf)
  
  def isTrivial(): Boolean = global_condition == APATrue() && pf == APAEmptySplitCondition()

  def input_variables = ((global_condition.input_variables ++ pf.input_variables) -- (input_assignment flatMap (_.input_variables))).removeDuplicates
  
  def conditionBodyToCommonString(rm: RenderingMode) = (global_condition, pf) match {
    case (_, APAEmptySplitCondition()) => global_condition.toString
    case (APATrue(), _) => pf.toString
    case _ => "("+global_condition.toString+") "+rm.and_symbol+" ("+pf.toString+")"
  }
  def conditionToCommonString = APASynthesis.rendering_mode match {
    case RenderingScala() => conditionToScalaString
    case RenderingPython() => conditionToPythonString
  }
  def conditionToScalaString = input_assignment match {
    case Nil => conditionBodyToCommonString(APASynthesis.rendering_mode)
    case _ => "{"+(input_assignment map (_.toCommonString("")) reduceLeft (_+";"+_)) + ";"+conditionBodyToCommonString(APASynthesis.rendering_mode)+"}"
  }
  def conditionToPythonString = {
    def conditionToPythonString_aux(input_assignment: List[InputAssignment]):String = input_assignment match {
      case Nil => conditionBodyToCommonString(APASynthesis.rendering_mode)
      case (assignment::q) =>
        "(lambda "+assignment.varToPythonString+": "+conditionToPythonString_aux(q)+")("+assignment.valToPythonString+")"
    }
    conditionToPythonString_aux(input_assignment)
  }
  
  def toCommonString = conditionToCommonString
  override def toString = toCommonString
  
  def execute(l: Map[InputVar, Int]): Boolean = {
    var input_value_map = l
    input_assignment foreach {
      case SingleInputAssignment(v, t) => val input_value_assignment = APAAbstractProgram.toAPAInputAssignment(input_value_map)
      t.replaceList(input_value_assignment) match {
        case APAInputCombination(i, Nil) => input_value_map += (v -> i) 
        case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
      }
      case BezoutInputAssignment(vl, tl) => val input_value_assignment = APAAbstractProgram.toAPAInputAssignment(input_value_map)
        val bezout_coefs:List[Int] = tl map (_.replaceList(input_value_assignment)) map {
          case APAInputCombination(i, Nil) => i
          case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
        }
        // Double zip and add all assignments to variables
        (vl zip Common.bezoutWithBase(1, bezout_coefs)) map { case (l1, l2) => l1 zip l2 } foreach { _ foreach { input_value_map += _ } }
    }
    global_condition.replaceListInput(APAAbstractProgram.toAPAInputAssignment(input_value_map)) match {
      case APATrue() => pf.execute(input_value_map)
      case APAFalse() => false
      case t =>
        throw new Exception ("Could not find the truth value of "+this+"\n under the mapping "+input_value_map+".\n Got the result: "+t)  
    }
  }
}

sealed abstract class APASplitCondition extends APAAbstractCondition {
  override def toString = toStringGeneral(APASynthesis.rendering_mode)
  
  def toStringGeneral(rm: RenderingMode):String
  def toCommonString:String = toStringGeneral(APASynthesis.rendering_mode)
}

case class APACaseSplitCondition(csl: List[APAAbstractCondition]) extends APASplitCondition { // ~= disjunction of all conditions ( c1 || c2 || c3 ... )
  def input_variables = (csl flatMap (_.input_variables)).removeDuplicates
  def execute(l: Map[InputVar, Int]): Boolean = csl exists (_.execute(l))
  def toStringGeneral(rm: RenderingMode):String = csl map { t => ("("+(t.toCommonString)+")") } reduceLeft (_ + " "+rm.or_symbol+" " + _)
  def toCondition: APACondition = APACondition(Nil, APATrue(), this)
}

case class APAEmptySplitCondition() extends APASplitCondition { // ~= true
  def input_variables = Nil
  def execute(l: Map[InputVar, Int]): Boolean = true
  def toStringGeneral(rm: RenderingMode) = ""
}

case class APAForCondition(vl: List[InputVar], lower_range: APAInputTerm, upper_range: APAInputTerm, global_condition: APACondition) extends APASplitCondition { // ~= true if global_condition holds for one tuple in the hypercube
  def input_variables = (global_condition.input_variables) -- vl

  // Need to specialize for each programmation language,
  def toStringGeneral(rm: RenderingMode):String = {
    rm match {
      case RenderingScala() => toScalaString
      case RenderingPython() => toPythonString
    }
  }
  def varsToString(vl : List[InputVar]) : String = vl match {
    case Nil => ""
    case (v::Nil) => v.name
    case (v::q) => "("+v.name+","+varsToString(q)+")" 
  }
  
  def toPythonString:String = {
    val basic_range = "xrange("+lower_range+", 1 + "+upper_range+")" 
    val list_ranges = "("+varsToString(vl)+" "+ (vl map { case i => "for "+i.name+" in "+basic_range}).reduceLeft(_ + " " + _) + ")"
    val exists_construct = "lambda a, "+varsToString(vl)+": a or "+ global_condition.toCommonString
    val condition = "reduce("+exists_construct+", "+list_ranges+", False)"
    condition
  }
  
  def toScalaString:String = {
    val basic_range = "("+lower_range+" to "+upper_range+")" 
    var ranges = basic_range
    vl.tail foreach {k =>
      ranges = ranges + " flatMap { t => "+basic_range+" map { i => (i, t) } } "
    }
    
    val expanded_vars = varsToString(vl)
    val find_string = ranges + " exists { case "+expanded_vars+" => "
    val cond_string = global_condition.toCommonString
    val match_string = " }"
    (find_string::cond_string::match_string::Nil).reduceLeft((_ + _))
  }
  def execute(l: Map[InputVar, Int]): Boolean = {
    if(global_condition == APACondition.False) return false
    val lr:Int = lower_range.replaceList(APAAbstractProgram.toAPAInputAssignment(l)) match {
      case APAInputCombination(k, Nil) => k
      case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+l)
    }
    val ur:Int = upper_range.replaceList(APAAbstractProgram.toAPAInputAssignment(l)) match {
      case APAInputCombination(k, Nil) => k
      case t =>
        throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+l)
    }
    val basic_range = (lr to ur)
    def possible_assignments(vl: List[InputVar], i: Int, current_assignment: List[(InputVar, Int)]) : Stream[List[(InputVar, Int)]] = vl match {
      case Nil => Stream(current_assignment)
      case (v::q) if i > ur => Stream()
      case (v::q) => possible_assignments(q, lr, (v, i)::current_assignment) append possible_assignments(vl, i+1, current_assignment) 
    } 
    val assignments = possible_assignments(vl, lr, Nil)
    
    assignments exists { assignments =>
      global_condition.execute(l ++ assignments)
    }
  }
}
