package synthesis



object APAAbstractProgram {
  def toAPAInputAssignment(imap : Map[InputVar, Int]):List[(InputVar, APAInputCombination)] =
    imap.toList map {case (v, i) => (v, APAInputCombination(i, Nil))}
  def toAPAOutputAssignment(imap : Map[OutputVar, Int]):List[(OutputVar, APACombination)] =
    imap.toList map {case (v, i) => (v, APACombination(APAInputCombination(i, Nil), Nil))}
    //Combines the two sentences, adding a "\n" if needed
  def combineSentences(s1: String, s2: String):String = (if(s1.endsWith("\n") || s1 == "") s1 else s1 + "\n") + s2
  
  def propagation_delete_temp(
      input_assignments : List[InputAssignment],
      output_assignments : List[(OutputVar, APATerm)],
      assignments_to_propagate_input : List[(InputVar, APAInputCombination)],
      assignments_to_propagate_output : List[(OutputVar, APACombination)],
      interesting_input_variables : List[InputVar], //Variables appearing in a split for example.
      interesting_output_variables : List[OutputVar])
        : (List[InputAssignment], List[(OutputVar, APATerm)]) = 
    recursive_propagation_delete_temp(input_assignments,
                                      output_assignments,
                                      assignments_to_propagate_input,
                                      assignments_to_propagate_output,
                                      interesting_input_variables,
                                      interesting_output_variables, Nil, Nil)

  def recursive_propagation_delete_temp(
      input_assignments : List[InputAssignment],
      output_assignments : List[(OutputVar, APATerm)],
      assignments_to_propagate_input : List[(InputVar, APAInputCombination)],
      assignments_to_propagate_output : List[(OutputVar, APACombination)],
      interesting_input_variables : List[InputVar],
      interesting_output_variables : List[OutputVar],
      input_assignments_new : List[InputAssignment],
      output_assignments_new : List[(OutputVar, APATerm)]
  )
        : (List[InputAssignment], List[(OutputVar, APATerm)]) = {
      // First: input assignments and then output assignments
      input_assignments match {
        case Nil => 
          output_assignments match {
            case Nil => (input_assignments_new.reverse, output_assignments_new.reverse)
            case (v, pac@APACombination(_, _))::q => 
              pac.replaceListInput(assignments_to_propagate_input).replaceList(assignments_to_propagate_output) match {
              case t@APACombination(_, _) =>
                if(interesting_output_variables contains v) { // yes ! let's keep this variable
                  recursive_propagation_delete_temp(Nil, q,
                                                    assignments_to_propagate_input,
                                                    assignments_to_propagate_output ++ ((v,t)::Nil),
                                                    interesting_input_variables,
                                                    interesting_output_variables,
                                                    input_assignments_new,
                                                    (v, t)::output_assignments_new)
                } else { // Not interesting to keep this variable. Just replace its content.
                  recursive_propagation_delete_temp(Nil, q,
                                                    assignments_to_propagate_input,
                                                    assignments_to_propagate_output ++ ((v,t)::Nil),
                                                    interesting_input_variables,
                                                    interesting_output_variables,
                                                    input_assignments_new, output_assignments_new)
                }
              // The term is not affine anymore, so we keep it without replacing.
              case t => recursive_propagation_delete_temp(Nil, q,
                                                          assignments_to_propagate_input,
                                                          assignments_to_propagate_output,
                                                          interesting_input_variables,
                                                          interesting_output_variables,
                                                          input_assignments_new,
                                                          (v, t)::output_assignments_new)
            }
           // The term is not affine, so we keep it without replacing.
            case (v, t)::q =>
              recursive_propagation_delete_temp(Nil, q,
                                                assignments_to_propagate_input,
                                                assignments_to_propagate_output,
                                                interesting_input_variables,
                                                interesting_output_variables,
                                                input_assignments_new,
                                                (v, t)::output_assignments_new)
          }
        // On input_assignments : they can be useful if case disjunctions, so we always keep them.
        // OptimizeMe : If not used in case disjunction, remove input variables.
        case (ass@SingleInputAssignment(v, pac@APAInputCombination(_, _)))::q =>
          val keep_assigment = interesting_input_variables contains v
          pac.replaceList(assignments_to_propagate_input) match {
            case t@APAInputCombination(_, _) => // We propagate everything.
              recursive_propagation_delete_temp(q, output_assignments,
                                                assignments_to_propagate_input ++ ((v,t)::Nil),
                                                assignments_to_propagate_output,
                                                interesting_input_variables,
                                                interesting_output_variables,
                                                (if(keep_assigment) (ass::input_assignments_new) else input_assignments_new),
                                                output_assignments_new)
           // Should not happen
           case t => throw new Error("Honestly, I don't see how an input combination" + pac + "could be reduced to something else like" + t + ", but it happened.")
          }
        case assignment::q =>
          assignment.replaceList(assignments_to_propagate_input) match {
            case Nil => throw new Error("In theory it cannot come up to this point")
            case new_assignment::Nil => 
              recursive_propagation_delete_temp(q, output_assignments,
                                            assignments_to_propagate_input,
                                            assignments_to_propagate_output,
                                            interesting_input_variables,
                                            interesting_output_variables,
                                            new_assignment::input_assignments_new,
                                            output_assignments_new)
            case l =>
              recursive_propagation_delete_temp(l ++ q, output_assignments,
                                            assignments_to_propagate_input,
                                            assignments_to_propagate_output,
                                            interesting_input_variables,
                                            interesting_output_variables,
                                            input_assignments_new,
                                            output_assignments_new)
          }
      }
      
    }
}

sealed abstract class APAAbstractProgram {
  def toCommonString(indent: String): String
  def execute(l: Map[InputVar, Int]): Map[OutputVar, Int]
  def input_variables: List[InputVar]
}

abstract class APASplit extends APAAbstractProgram

case class APAFalseSplit() extends APASplit { // ~= assert(false);
  def toCommonString(indent: String) = ""
  def execute(l: Map[InputVar, Int]) = Map[OutputVar, Int]()
  def input_variables = Nil
}

case class APAEmptySplit() extends APASplit { // ~= NOOP
  def toCommonString(indent: String) = ""
  def execute(l: Map[InputVar, Int]) = Map[OutputVar, Int]()
  def input_variables = Nil
}

object APACaseSplit {
  def variable_define(indent: String, tuple_variables: String):String = {
    APASynthesis.rendering_mode match {
      case RenderingPython() =>
        indent // All variables will be described inside the program.
      case RenderingScala() =>
        indent + "val "+ tuple_variables +" = "
    }
  }
  def optimized(programs: List[(APACondition, APAProgram)]): APACaseSplit = {
    val new_programs = programs remove {
      case (cond, prog) =>
        cond.global_condition == APAFalse() || (cond.pf match {
          case t:APAForCondition => t.global_condition == APAFalse()
          case _ => false
        })
    }
    val reduced_programs = new_programs find { // Find some trivial solution if it exists.
      case (cond, prog) => cond.isTrivial()
    } match {
      case Some(a) => a::Nil
      case _ => new_programs
    }
    APACaseSplit(reduced_programs)
  }
}

case class APACaseSplit(programs: List[(APACondition, APAProgram)]) extends APASplit {
  def input_variables = (programs flatMap (_._2.input_variables)).removeDuplicates
  override def toString = toCommonString("  ")
  def toProgram: APAProgram = programs match {
    case Nil => APAProgram.empty
    case (c, p)::Nil => p
    case (c, p)::q =>
      APAProgram(p.input_variables, Nil, this, Nil, p.output_variables)
  }
  def toCommonString(indent: String) = {
    APASynthesis.rendering_mode match {
      case RenderingScala() => toScalaString(indent)
      case RenderingPython() => toPythonString(indent)
    }
  }
  def toPythonString(indent: String) = {
    val indent2 = indent + "  "
    (programs match {
      case Nil => ""
      case ((cond, pap)::Nil) =>
        pap.innerCommonContent(indent)
      case ((cond, pap)::_::q) =>
        val error_result = pap.errorResultCommon(RenderingPython())
        val prefix = APACaseSplit.variable_define(indent, pap.resultCommonContent(""))
        prefix +
        ((programs map {
          case (cond, pap) =>
            val prog_if = "if "+(cond.toCommonString)+":"
            val prog_ifthen = pap.innerCommonContent(indent2)
            //val prog_ifthenresult = pap.resultCommonContent(indent2)
            val prog_ifend = indent
            (prog_if::prog_ifthen::prog_ifend::Nil).reduceLeft(APAAbstractProgram.combineSentences(_, _))
        })++(("se:\n"+indent2+error_result)::Nil)).reduceLeft( _ + "el" + _)
    })
  }
  
  def toScalaString(indent: String) = {
    val indent2 = indent + "  "
    (programs match {
      case Nil => ""
      case ((cond, pap)::Nil) =>
        pap.innerCommonContent(indent)
      case ((cond, pap)::_::q) =>
        val error_result = pap.errorResultCommon(RenderingScala())
        val prefix = APACaseSplit.variable_define(indent, pap.resultCommonContent(""))
        prefix +
        ((programs map {
          case (cond, pap) =>
            val prog_if = "if("+(cond.conditionToScalaString)+") {"
            val prog_ifthen = pap.innerCommonContent(indent2)
            val prog_ifthenresult = pap.resultCommonContent(indent2)
            val prog_ifend = indent + "}"
            (prog_if::prog_ifthen::prog_ifthenresult::prog_ifend::Nil).reduceLeft(APAAbstractProgram.combineSentences(_, _))
        })++(("{ "+error_result+" }")::Nil)).reduceLeft( _ + " else " + _)
    })
  }
  def execute(l: Map[InputVar, Int]): Map[OutputVar, Int] = {
    programs foreach {
      case (cond, prog) =>
        if(cond.execute(l)) return prog.execute(l)
    }
    Map[OutputVar, Int]()
  }
}

object APAForSplit {
}

case class APAForSplit(vl: List[InputVar], lower_range: APAInputTerm, upper_range: APAInputTerm, condition: APACondition, program: APAProgram) extends APASplit {
  override def toString = toCommonString("  ")
  def input_variables = (program.input_variables) -- vl
  
  def toCommonString(indent: String) = {
    APASynthesis.rendering_mode match {
      case RenderingScala() => toScalaString(indent)
      case RenderingPython() => toPythonString(indent)
    }
  }
  
  def varsToString(vl : List[InputVar]) : String = vl match {
    case Nil => ""
    case (v::Nil) => v.name
    case (v::q) => "("+v.name+","+varsToString(q)+")" 
  }
  
  def toPythonString(indent: String) = {
    val condition_variable = "_condition_"
    
    val indent2 = indent + "  "
    val basic_range = "xrange("+lower_range+", 1 + "+upper_range+")"
    val vs = vl match {
      case v::Nil => "("+varsToString(vl)+",)"
      case _ => varsToString(vl)
    }
    val list_ranges = "("+vs+" "+ (vl map { case i => "for "+i.name+" in "+basic_range}).reduceLeft(_ + " " + _) + ")"
    val exists_construct = "lambda a, "+vs+": a or ("+ condition.toCommonString+" and "+vs+")"
    val finding_term = "reduce("+exists_construct+", "+list_ranges+", False)"
    val line_condition = indent + condition_variable+" = "+finding_term
    val line_if        = indent + "if "+condition_variable+":"
    val line_assign    = indent + "  " + vs + " = "+condition_variable
    val prog_string    = program.innerCommonContent(indent2)
    val line_else      = indent + "else:"
    val line_else_prog = indent2 + program.errorResultCommon(RenderingPython())
    (line_condition::line_if::line_assign::prog_string::line_else::line_else_prog::Nil).reduceLeft(APAAbstractProgram.combineSentences(_, _))
  }
  
  def toScalaString(indent: String) = {
    val indent2 = indent + "  "
    val basic_range = "(("+lower_range+") to ("+upper_range+"))" 
    var ranges = basic_range
    vl.tail foreach {k =>
      ranges = ranges + " flatMap { t => "+basic_range+" map { i => (i, t) } } "
    }
    val expanded_vars = varsToString(vl)
    val find_string = indent + "val " + program.resultCommonContent("") + " = " + ranges + " find { case "+expanded_vars+" => "
    val cond_string = indent2 + condition.toCommonString
    val match_string = indent+"} match {"
    val case_string = indent2+"case Some("+expanded_vars+") => "
    val prog_string = program.innerCommonContent(indent2)
    val result_string = program.resultCommonContent(indent2)
    val error_result = program.errorResultCommon(RenderingScala())
    val end_string = indent2+"case None => "+error_result+"\n"+indent+"}"
    (find_string::cond_string::match_string::case_string::prog_string::result_string::end_string::Nil).reduceLeft(APAAbstractProgram.combineSentences(_, _))
  }
  def execute(l: Map[InputVar, Int]): Map[OutputVar, Int] = {
    val lr:Int = lower_range.replaceList(APAAbstractProgram.toAPAInputAssignment(l)) match {
      case APAInputCombination(k, Nil) => k
      case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+l)
    }
    val ur:Int = upper_range.replaceList(APAAbstractProgram.toAPAInputAssignment(l)) match {
      case APAInputCombination(k, Nil) => k
      case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+l)
    }
    val basic_range = (lr to ur)
    def possible_assignments(vl: List[InputVar], i: Int, current_assignment: List[(InputVar, Int)]) : Stream[List[(InputVar, Int)]] = vl match {
      case Nil => Stream(current_assignment)
      case (v::q) if i > ur => Stream()
      case (v::q) => possible_assignments(q, lr, (v, i)::current_assignment) append possible_assignments(vl, i+1, current_assignment) 
    } 
    val assignments = possible_assignments(vl, lr, Nil)
    
    assignments find { assignments =>
      condition.execute(l ++ assignments)
    } match {
      case Some(assignments) =>
        program.execute(l ++ assignments)
      case None => //throw new Error("Could not find a satisfying "+vl+" in ["+lower_range+","+upper_range+"] for "+condition.toScalaString)
        program.execute(l ++ (vl map { case v => (v -> 0)})) 
    }
  }
}

// Programs
object APAProgram {
  def empty:APAProgram = APAProgram(Nil, Nil, APAEmptySplit(), Nil, Nil)
  def optimized(input_variables: List[InputVar],
                input_assignment: List[InputAssignment],
                case_splits: APASplit,
                output_assignment: List[(OutputVar, APATerm)],
                output_variables: List[OutputVar]):APAProgram = {
    val final_output_variables = output_variables
    val interesting_input_variables = (case_splits.input_variables ++ (output_assignment map (_._2) flatMap (_.input_variables))).removeDuplicates
    // Let's propagate assignments that are temporary
    val (reduced_input_assignments, reduced_output_assignments) = APAAbstractProgram.propagation_delete_temp(input_assignment, output_assignment, Nil, Nil, interesting_input_variables, output_variables)
    APAProgram(input_variables, reduced_input_assignments, case_splits, reduced_output_assignments, output_variables)
  }
  def merge_disjunction(input_variables : List[InputVar],
                        output_variables: List[OutputVar],
                        programs_conditions: List[(APACondition, APAProgram)]): (APACondition, APAProgram) = {
    //Adds the global precondition the disjunction fo the case split conditions.
    val programs_conditions_filtered = programs_conditions remove (_._1.global_condition == APAFalse())
    programs_conditions_filtered find { case (c, p) => c.isTrivial() } match {
      case Some(complete_program) => complete_program
      case None =>
        programs_conditions_filtered match {
          case Nil => (APACondition.False, APAProgram.empty)
          case a::Nil => a
          case _ => 
            val splitted_conditions:List[APACondition] = programs_conditions_filtered map (_._1)
            val splitted_formulas:List[APAFormula] = splitted_conditions map (_.global_condition)
            val final_precondition = APACaseSplitCondition(splitted_conditions).toCondition
            val final_program = APACaseSplit(programs_conditions_filtered).toProgram
            (final_precondition, final_program)
        }
    }
  }
  def outputAssignmentToString(variable: OutputVar, value: APATerm):String = {
    APASynthesis.rendering_mode match {
      case RenderingScala() => "val "+ variable.name + " = " + value.toCommonString
      case RenderingPython() => variable.name + " = " + value.toCommonString
    }
  }
}

//Top-level program, with the definition of the input variables and output variables.
case class APAProgram(input_variables: List[InputVar],
                      input_assignment: List[InputAssignment],
                      case_splits: APASplit,
                      output_assignment: List[(OutputVar, APATerm)],
                      output_variables: List[OutputVar]) extends APAAbstractProgram {
  var name="result"
  def setName(new_name: String) = name = new_name
  
  override def toString = toCommonString("  ")
  def toCommonString(indent: String):String = APASynthesis.rendering_mode match {
    case RenderingScala() => toScalaString(indent)
    case RenderingPython() => toPythonString(indent)
  }
  
  def innerCommonContent(indent:String):String = {
    val prog_input = InputAssignment.listToCommonString(input_assignment, indent)
    val prog_case_split = case_splits.toCommonString(indent)
    val prog_output = output_assignment map {
      case (i, t) => indent+APAProgram.outputAssignmentToString(i, t)
    } match {
      case Nil => ""
      case l => l reduceLeft (APAAbstractProgram.combineSentences(_, _))
    }
    (prog_input::prog_case_split::prog_output::Nil).reduceLeft(APAAbstractProgram.combineSentences(_, _))
  }
  
  def resultCommonContent(indent:String):String = {
    indent+(output_variables match {
      case Nil => "()"
      case (a::Nil) => a.name
      case l => "(" + (l map (_.name) sort {_ < _} reduceLeft (_+", "+_)) + ")"
    })
  }
  
  def errorResultCommon(rm: RenderingMode): String = {
    APASynthesis.rendering_mode match {
      case RenderingPython() => errorResultPython(rm)
      case RenderingScala() => errorResultScala(rm)
    }
  }
  
  def errorResultScala(rm: RenderingMode): String = {
    if(APASynthesis.run_time_checks) {
      rm.error_string
    } else {
      output_variables match {
        case Nil => "()"
        case (a::Nil) => "0"
        case l => "("+(l map { _ => "0"} reduceLeft(_ + ", " + _))+")"
      }
    }
  }
  def errorResultPython(rm: RenderingMode): String = {
    if(APASynthesis.run_time_checks) {
      rm.error_string
    } else {
      output_variables match {
        case Nil => "()"
        case (a::Nil) => a.name + " = 0"
        case l => "("+(l map (_.name ) reduceLeft (_ + ", " + _)) + ") = (" + (l map { _ => "0"} reduceLeft (_ + ", " + _)) + ")"
      }
    }
  }
  def inputCommonContent:String = APASynthesis.rendering_mode match {
    case RenderingScala() => inputScalaContent
    case RenderingPython() => inputPythonContent
  }
  
  def inputScalaContent:String = input_variables match {
    case Nil => ""
    case l => (input_variables map (_.name + " : Int") reduceLeft (_+", "+_))
  }
  def inputPythonContent:String = input_variables match {
    case Nil => ""
    case l => (input_variables map (_.name) reduceLeft (_+", "+_))
  }
  
  def toPythonString(indent: String):String = {
    val function_definition = "def "+name+"("+inputCommonContent+"):"
    val inner_content = innerCommonContent(indent)
    val result = indent + "return " + resultCommonContent("")
    (function_definition::inner_content::result::Nil).reduceLeft(APAAbstractProgram.combineSentences(_, _))
  }
  
  def toScalaString(indent: String):String = {
    val return_type = output_variables match {
      case Nil => "()"
      case (a::Nil) => "Int"
      case l => "("+(l map {_=>"Int"} reduceLeft (_ + ", " + _)) +")"
    }
    val function_definition = "def "+name+"("+inputCommonContent+"):" + return_type + " = {"
    val inner_content= innerCommonContent(indent)
    val result = resultCommonContent(indent)
    var prog = function_definition
    (function_definition::inner_content::result::"}"::Nil).reduceLeft(APAAbstractProgram.combineSentences(_, _))
  }
  def execute(l: Map[InputVar, Int]): Map[OutputVar, Int] = {
    var input_value_map = l
    input_assignment foreach {
      case SingleInputAssignment(v, t) => val input_value_assignment = APAAbstractProgram.toAPAInputAssignment(input_value_map)
      t.replaceList(input_value_assignment) match {
        case APAInputCombination(i, Nil) => input_value_map += (v -> i) 
        case t =>
          throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
      }
      case BezoutInputAssignment(vl, tl) => val input_value_assignment = APAAbstractProgram.toAPAInputAssignment(input_value_map)
        val bezout_coefs:List[Int] = tl map (_.replaceList(input_value_assignment)) map {
          case APAInputCombination(i, Nil) => i
          case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
        }
        // Double zip and add all assignments to variables
        (vl zip Common.bezoutWithBase(1, bezout_coefs)) map { case (l1, l2) => l1 zip l2 } foreach { _ foreach { input_value_map += _ } }
    }
    var output_value_map = case_splits.execute(input_value_map)
    val input_assignments_listed = APAAbstractProgram.toAPAInputAssignment(input_value_map)
    output_assignment foreach {
      case (v, t) =>
        t.replaceListInput(input_assignments_listed).replaceList(APAAbstractProgram.toAPAOutputAssignment(output_value_map)) match {
        case APACombination(APAInputCombination(i, Nil), Nil) => output_value_map += (v -> i) 
        case g =>
          throw new Exception("Was not able to reduce term to integer : "+t+"\nunder the mappings "+input_value_map+" and "+output_value_map+"\nGot : "+g)
      }
    }
    Map[OutputVar, Int]() ++ (output_variables map {case v => (v, (output_value_map(v)))})
  }
}
  
