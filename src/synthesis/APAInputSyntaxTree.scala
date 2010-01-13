package synthesis

// dummy
object APAInputSyntaxTree

object APAInputTerm {
  def partitionInteger(l: List[APAInputTerm]): (List[Int], List[APAInputTerm]) = l match {
    case Nil => (Nil, Nil)
    case (APAInputCombination(n, Nil)::q) =>
      val (a, b) = partitionInteger(q)
      (n::a, b)
    case (p::q) =>
      val (a, b) = partitionInteger(q)
      (a, p::b)
  }
}

/*****************
 *  Input terms  *
 *****************/

trait ConvertibleToInputTerm {
  implicit def toInputTerm():APAInputTerm 
}

sealed abstract class APAInputTerm extends SignAbstraction {
  // OptimizeMe : Store when it's already simplified in order not to compute two times the same thing 
  def simplified:APAInputTerm
  def input_variables: List[InputVar]
  def +(that : APACombination):APACombination = that + APACombination(this)
  def -(that : APACombination):APACombination = -that + APACombination(this)
  def *(that : APACombination):APACombination = that * this
  
  def +(that : APAInputTerm): APAInputTerm = APAInputAddition(this, that).simplified
  def /(that : APAInputTerm): APAInputTerm = APAInputDivision(this, that).simplified
  def *(that : APAInputTerm): APAInputTerm = APAInputMultiplication(this, that).simplified
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm

  def replaceList(lxt : List[(InputVar, APAInputTerm)]): APAInputTerm = {
    lxt.foldLeft(this){ case (result, (x, t)) => result.replace(x, t) }
  }
  
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAInputTerm = {
    (this, t1, -t1) match {
      case (t0:APAInputCombination, t1:APAInputCombination, _) if t0 == t1 =>
        val result = t1.assumeSign(s).propagateSign(this)
        result
      case (t0:APAInputCombination, _, mt1:APAInputCombination) if t0 == mt1 =>
        val result = (-t1.assumeSign(s)).propagateSign(this)
        result
      case (t0:APAInputCombination, t1:APAInputCombination, mt1:APAInputCombination) =>
        this
      case _ =>
        this
    }
  }
  
  def -(that : APAInputTerm): APAInputTerm =  (this, that) match {
    case (t1: APAInputCombination, t2: APAInputCombination) => t1 - t2
    case _ => this+(that*APAInputCombination(-1))
  }
  def unary_-(): APAInputTerm = APAInputCombination(0, Nil) - this
  def toInt: Int = this match {
    case APAInputCombination(i, Nil) => i
    case _ =>
      throw new Exception(this + " cannot be converted to an integer")
  }
  
  override def toString = toGeneralString
  
  def toGeneralString: String = APASynthesis.rendering_mode match {
    case rm@RenderingPython() => toPythonString(rm)
    case rm@RenderingScala() => toScalaString(rm)
  }
  
  def toPythonString(rm: RenderingMode): String = this match {
    case APAInputLCM(l) => rm.lcm_symbol+"(["+(l map (_.toCommonString(rm)) reduceLeft (_ + "," + _)) +"])"
    case APAInputGCD(l) => rm.gcd_symbol+"(["+(l map (_.toCommonString(rm)) reduceLeft (_ + "," + _)) +"])"
    case _ => toCommonString(rm)
  }
  def toScalaString(rm: RenderingMode): String = this match {
    case APAInputLCM(l) => rm.lcm_symbol+"(List("+(l map (_.toCommonString(rm)) reduceLeft (_ + "," + _)) +"))"
    case APAInputGCD(l) => rm.gcd_symbol+"(List("+(l map (_.toCommonString(rm)) reduceLeft (_ + "," + _)) +"))"
    case _ => toCommonString(rm)
  }
  
  def toCommonString(rm:RenderingMode):String = this match {
    case APAInputMultiplication(Nil) => "1"
    case APAInputMultiplication(a::Nil) => a.toCommonString(rm)
    case APAInputMultiplication(l) => l map {
        case el =>
          val s = el.toCommonString(rm)
          if(((s indexOf '-') >= 0) || ((s indexOf '+') >= 0) || ((s indexOf '/') >= 0)) "("+s+")" else s
      } reduceLeft (_ + "*" + _)
    case APAInputDivision(Nil, ld) => "1/("+APAInputMultiplication(ld).toCommonString(rm)+")"
    case APAInputDivision(ln, Nil) => APAInputMultiplication(ln).toCommonString(rm)
    case APAInputDivision(ln, ld) =>
      val num = APAInputMultiplication(ln).toCommonString(rm)
      val den = APAInputMultiplication(ld).toCommonString(rm)
    val num_string = (if((num indexOf '+') >= 0 || (num indexOf '-') >= 0 || (num indexOf '+') >= 0) "("+num+")" else num )
    val den_string = (if((den indexOf '+') >= 0 || (den indexOf '-') >= 0 || (den indexOf '+') >= 0) "("+den+")" else den )
    num_string +"/"+den_string
    case APAInputAddition(l) => l map {
        case el =>
          val s = el.toCommonString(rm)
          if((s indexOf '-') >= 0) "("+s+")" else s
      } reduceLeft (_ + " + " + _)
    case APAInputAbs(e) => rm.abs_symbol + "("+e.toCommonString(rm)+")"
    case APAInputLCM(Nil) =>
      throw new Exception("What is this lcm that has not been simplified ??")
    case APAInputLCM(l) => rm.lcm_symbol+"(List("+(l map (_.toCommonString(rm)) reduceLeft (_ + "," + _)) +"))"
    case APAInputGCD(l) => rm.gcd_symbol+"(List("+(l map (_.toCommonString(rm)) reduceLeft (_ + "," + _)) +"))"
    case t:APAInputCombination => t.toNiceString
    case APAInputMod(operand, divisor) =>
      val num = operand.toCommonString(rm)
      val den = operand.toCommonString(rm)
      val num_string = (if((num indexOf '+') >= 0 || (num indexOf '-') >= 0 || (num indexOf '+') >= 0) "("+num+")" else num )
      val den_string = (if((den indexOf '+') >= 0 || (den indexOf '-') >= 0 || (den indexOf '+') >= 0) "("+den+")" else den )
      val final_den_string = if(divisor.isPositive) den_string else (rm.abs_symbol+"("+den_string+")")
      rm.mod_function(num_string, final_den_string)
    //case _ => super.toString
  }
}

case class InputVar(name: String) extends SignAbstraction with ConvertibleToInputTerm with APAVariable {
  def normalClone():this.type = InputVar(name).asInstanceOf[this.type]
  def toInputTerm():APAInputCombination = {
    if(isZero) return APAInputCombination(0)
    APAInputCombination(this)
  }
  // Syntactic sugar
  //def +(pac : APACombination) = pac+APACombination(this)
  //def +(v : InputVar) = APACombination(v)+APACombination(this)
  //def +(v : OutputVar) = APACombination(v)+APACombination(this)
  //def *(i : Int) = APAInputCombination(0, (i, this)::Nil)
  //def *(that: APAInputTerm) = APAInputMultiplication(APAInputCombination(this), that)
}

object APAInputCombination {
  def apply(i: Int):APAInputCombination = APAInputCombination(i, Nil)
  def apply(i: InputVar):APAInputCombination = APAInputCombination(0, (1, i)::Nil).propagateSign(i)
}

// Const_part does not contain any output variables
case class APAInputCombination(coefficient: Int, input_linear: List[(Int, InputVar)]) extends APAInputTerm {
  setSign(SignAbstraction.linearCombinationSign(coefficient, input_linear))

  def normalClone():this.type = APAInputCombination(coefficient, input_linear).asInstanceOf[this.type]

  def input_variables: List[InputVar] = input_linear map (_._2)
  // Sorting functions
  def by_InputVar_name(i1:(Int, InputVar), i2:(Int, InputVar)) : Boolean = (i1, i2) match {
    case ((_, InputVar(name1)), (_, InputVar(name2))) => name1 < name2
  }
  // Regrouping functions
  def fold_Inputvar_name(i:(Int, InputVar), regrouped_vars:List[(Int, InputVar)]):List[(Int, InputVar)] = (i, regrouped_vars) match {
    case (i, Nil) => i::Nil
    case ((coef1, InputVar(name1)), (coef2, InputVar(name2))::q) if name1 == name2 => (coef1 + coef2, InputVar(name1))::q
    case (i, q) => i::q 
  }
  
  override def propagateSign(s: SignAbstraction):this.type = { //Intercepts the sign propagation
    val result = (coefficient, input_linear) match {
      case (0, (i, v)::Nil) => 
        val new_v = v.assumeSign(SignAbstraction.multSign(SignAbstraction.mergeSign(this, s), SignAbstraction.number(i)))
        APAInputCombination(0, (i, new_v)::Nil)
      case _ => this
    }
    result.propagateSign_internal(s).asInstanceOf[this.type]
  }
  
  /// Simplified means that the variables are alphabetically sorted, that there are no null coefficients, and the gcd of all coefficients is 1.
  def simplified: APAInputCombination = {
    if(isZero) return APAInputCombination(0)
    val input_linear2 = (input_linear  sort by_InputVar_name ).foldRight[List[(Int, InputVar)]](Nil){ case (a, b) => fold_Inputvar_name(a, b)}
    val input_linear3: List[(Int, InputVar)] = input_linear2 match {
      case (i, v)::Nil => (i, v.assumeSign(SignAbstraction.multSign(this, SignAbstraction.number(i))))::Nil
      case _ => input_linear2
    }
    APAInputCombination(coefficient, input_linear3 remove { case (i, v) => i == 0 || v.isZero}).propagateSign(this)
  }
  def coefficient_list = (coefficient :: ((input_linear map (_._1)) ))
  def has_gcd_coefs: Boolean = coefficient_list exists (_ != 0)
  def gcd_coefs = Common.gcdlist(coefficient_list)
  def first_sign_present = coefficient_list find (_ != 0) match { case Some(i) => if(i > 0) 1 else -1; case None => 1}
  
  /// Division of this combination by an integer. Needs the coefficients to be divisible by i.
  def /(i : Int): APAInputCombination = {
    APAInputCombination(coefficient / i, input_linear map {t => (t._1 / i, t._2)}).assumeSign(SignAbstraction.multSign(this, SignAbstraction.number(i)))
  }
  def safelyDivisibleBy(i : Int): Boolean = {
    coefficient % i == 0 && (input_linear forall { case (k, v) => k % i == 0})
  }
  
  
  def /(that : APAInputCombination): APAInputTerm = {
    APAInputDivision(this, that).simplified
  }
  /// Multiplication by an integer
  def *(i : Int): APAInputCombination = {
    APAInputCombination(coefficient * i, input_linear map {t => (t._1 * i, t._2)}).assumeSign(SignAbstraction.multSign(this, SignAbstraction.number(i)))
  }
  def *(that : APAInputCombination): APAInputTerm = {
    APAInputMultiplication(this, that).simplified
  }
  /// Addition between two combinations
  def +(pac : APAInputCombination): APAInputCombination = pac match {
    case APAInputCombination(c, i) => 
      APAInputCombination(coefficient + c, input_linear ++ i).simplified.assumeSign(SignAbstraction.addSign(this, pac))
  }
  /// Substraction between two combinations
  def -(that : APAInputCombination): APAInputCombination = this + (that * (-1))
  /// Addition with a new variable and its coefficient
  def +(kv : (Int, InputVar)): APAInputCombination = this + APAInputCombination(0, kv::Nil)
  def +(k : Int): APAInputCombination = this + APAInputCombination(k, Nil)
  /// Substraction with a new variable and its coefficient
  def -(kv : (Int, InputVar)): APAInputCombination = this - APAInputCombination(0, kv::Nil)
  def -(k : Int): APAInputCombination = this + APAInputCombination(-k, Nil)
  override def unary_-(): APAInputCombination = (APAInputCombination(0, Nil) - this).propagateSign(SignAbstraction.oppSign(this))
  
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    val (input_linear_with_y, input_linear_without_y) = input_linear partition (_._2 == y)
    val pac_without_y = APAInputCombination(coefficient, input_linear_without_y)
    val total_y_coefficient = (input_linear_with_y map (_._1)).foldLeft(0)(_+_)
    val result = t match {
      case t:APAInputCombination =>
        pac_without_y + (t*total_y_coefficient)
      case _ =>
        APAInputAddition(pac_without_y, APAInputMultiplication(APAInputCombination(total_y_coefficient), t))
    }
    result.propagateSign(this)
  }
  
  override def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction) = {
    t1 match {
      case t@APAInputCombination(coefficient2, Nil) => this // Would be strange to arrive there.
      case t@APAInputCombination(coefficient2, (i, v)::l) => // i is not null,
        input_linear find (_._2 == v) match {
          case Some((i2, v2)) =>
            val t_assumed = t.assumeSign(s)
            val resultWithoutT = (this*i-t_assumed*i2) 
            val resultAddingT  =(t_assumed*i2)
            val resultMultipliedByI = resultWithoutT+resultAddingT
            val result = resultMultipliedByI/i
            result
          case None => this // This variable is not there, so we cannot conclude anything.
        }
      case _ => this
      
    }
  }

  override def toString = toNiceString
  
  def toNiceString:String = {
    def inputElementToString(kv : (Int, InputVar)) = kv._1 match {
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
    var i_string = input_linear match {
      case Nil => ""
      case a::l => l.foldLeft(inputElementToString(a)) { (s, t2) =>
        val t2s = inputElementToString(t2)
        s + (if(t2s.charAt(0) =='-') t2s else "+" + t2s)}
    }
    val s = makePlus(c_string::i_string::Nil)
    if(s == "") "0" else s
  }
}
object APAInputDivision {
  def apply(a: APAInputTerm, b: APAInputTerm): APAInputTerm = APAInputDivision(a::Nil, b::Nil).simplified
  def simplifyNumDenom(n: List[APAInputTerm], d:List[APAInputTerm]):APAInputTerm = {
    val (to_delete, n_ok) = n partition (d contains _)
    if(to_delete != Nil) {
      val (d_updated, to_be_nil) = d.foldLeft((to_delete, Nil:List[APAInputTerm])){
        case ((to_delete, collecter), el) =>
          if(to_delete contains el)
            (to_delete - el, collecter)
          else
            (to_delete, collecter ++ (el ::Nil))
      }
      APAInputDivision(n_ok, d_updated)
    } else {
      APAInputDivision(n, d)
    }
  }
}

//Internally, this representation is optimized to have the constant coefficients in the front
// That's of course if you don't create these lists yourself.
// Point: The denominator has to divide the numerator.
case class APAInputDivision(numerator: List[APAInputTerm], denominator : List[APAInputTerm]) extends APAInputTerm {
  setSign(SignAbstraction.divSign(SignAbstraction.multSign(numerator), SignAbstraction.multSign(denominator)))
  def normalClone():this.type = APAInputDivision(numerator, denominator).asInstanceOf[this.type]

  def simplified:APAInputTerm = {
    if(isZero) return APAInputCombination(0)
    val result = ((APAInputMultiplication(numerator).simplified, APAInputMultiplication(denominator).simplified) match {
      case (n, APAInputCombination(1, Nil)) => n
      case (n, d) if n == d => APAInputCombination(1, Nil)
      case (nm@APAInputMultiplication(n), dm@APAInputMultiplication(d)) => APAInputDivision.simplifyNumDenom(n, d)
      case (nm, dm@APAInputMultiplication(d)) => APAInputDivision.simplifyNumDenom(nm::Nil, d)
      case (nm@APAInputMultiplication(n), dm) => APAInputDivision.simplifyNumDenom(n, dm::Nil)
      case (nc@APAInputCombination(c, Nil), dc@APAInputCombination(i, Nil)) => APAInputCombination(c/i)
      case (nc@APAInputCombination(c, l), dc@APAInputCombination(i, Nil)) if nc.safelyDivisibleBy(i) => nc/i
      case (nc@APAInputCombination(c, l), dc@APAInputCombination(i, Nil)) => APAInputDivision(nc::Nil, dc::Nil)
      case (n, d) => APAInputDivision(n::Nil, d::Nil)
    })
    result.propagateSign(this)
  }
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    APAInputDivision(numerator map (_.replace(y, t)), denominator map (_.replace(y, t))).simplified.propagateSign(this)
  }
  def input_variables: List[InputVar] = {
    ((numerator flatMap (_.input_variables)) ++ (denominator flatMap (_.input_variables))).removeDuplicates
  }
}
object APAInputMultiplication {
  def apply(a: APAInputTerm*):APAInputTerm = APAInputMultiplication(a.toList).simplified
}
// When simplified, all coefficients are in the front.
case class APAInputMultiplication(operands: List[APAInputTerm]) extends APAInputTerm {
  //assert(operands.length > 1) // Else it does not make sense, it should have been simplified.
  setSign(SignAbstraction.multSign(operands))
  def normalClone():this.type = APAInputMultiplication(operands).asInstanceOf[this.type]
  
  def simplified:APAInputTerm = {
    if(isZero) return APAInputCombination(0)
    val result = operands flatMap (_.simplified match {
      case APAInputMultiplication(l) => l map (_.assumeNotzerobility(this))
      case APAInputCombination(1, Nil) => Nil
      case t => List(t.assumeNotzerobility(this))
    }) match {
      case Nil => APAInputCombination(1, Nil)
      case a::Nil => a
      case l => 
        APAInputTerm.partitionInteger(l) match {
          case (Nil, l) =>
            APAInputMultiplication(l)
          case (integers, not_input_combinations) =>
            ((integers reduceLeft (_ * _)), not_input_combinations) match {
              case (0, _) => APAInputCombination(0)
              case (a, Nil) => APAInputCombination(a)
              case (a, (t:APAInputCombination)::q) => APAInputMultiplication((t*a)::q)
              case (a, _) => val s = APAInputCombination(a)::not_input_combinations
                APAInputMultiplication(s)
            }
        }
    }
    result.propagateSign(this)
  }

  override def propagateSign(s: SignAbstraction):this.type = { //Intercepts the sign propagation
    if(s.isNotZero) {
      val new_operands = operands map (_.assumeNotzerobility(s))
      APAInputMultiplication(new_operands).propagateSign_internal(s).asInstanceOf[this.type]
    } else {
      APAInputMultiplication(operands).propagateSign_internal(s).asInstanceOf[this.type]
    }
  }
  
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    APAInputMultiplication(operands map (_.replace(y, t))).propagateSign(this).simplified
  }
  def input_variables: List[InputVar] = {
    (operands flatMap (_.input_variables)).removeDuplicates
  }
}

object APAInputAddition {
  def apply(a: APAInputTerm*):APAInputAddition = APAInputAddition(a.toList)
}
case class APAInputAddition(l: List[APAInputTerm]) extends APAInputTerm {
  setSign(SignAbstraction.addSign(l))
  def normalClone():this.type = APAInputAddition(l).asInstanceOf[this.type]
  
  def partitionInputCombination(l: List[APAInputTerm]): (List[APAInputCombination], List[APAInputTerm]) = l match {
    case Nil => (Nil, Nil)
    case ((t@APAInputCombination(_, _))::q) =>
      val (a, b) = partitionInputCombination(q)
      (t::a, b)
    case (p::q) =>
      val (a, b) = partitionInputCombination(q)
      (a, p::b)
  }
  def simplified:APAInputTerm = {
    if(isZero) return APAInputCombination(0)
    val result = l flatMap (_.simplified match {
      case APAInputAddition(l) => l
      case APAInputCombination(0, Nil) => Nil
      case t => List(t)
    }) match {
      case Nil => APAInputCombination(0, Nil)
      case a::Nil => a
      case l => 
        partitionInputCombination(l) match {
          case (Nil, l) =>
            APAInputAddition(l)
          case (input_combinations, not_input_combinations) =>
            ((input_combinations reduceLeft (_ + _)), not_input_combinations) match {
              case (a, Nil) => a
              case (a, _) => val s = a::not_input_combinations
                APAInputAddition(s)
            }
            
        }
    }
    result.propagateSign(this)
  }
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    APAInputAddition(l map (_.replace(y, t))).propagateSign(this).simplified
  }
  def input_variables: List[InputVar] = {
    (l flatMap (_.input_variables)).removeDuplicates
  }
}

case class APAInputAbs(arg: APAInputTerm) extends APAInputTerm {
  setSign(SignAbstraction.absSign(arg))
  def normalClone():this.type = APAInputAbs(arg).asInstanceOf[this.type]
  def simplified:APAInputTerm = {
    if(isZero) return APAInputCombination(0)
    val result = arg.simplified match {
      case t if t.isPositiveZero => t
      case APAInputCombination(i, Nil) => APAInputCombination(Math.abs(i), Nil)
      case t =>
        APAInputAbs(t)
    }
    result.propagateSign(this)
  }
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    val result = APAInputAbs(arg.replace(y, t)).simplified
    result.propagateSign(this)
  }
  def input_variables: List[InputVar] = {
    arg.input_variables
  }
}

case class APAInputGCD(l: List[APAInputTerm]) extends APAInputTerm {
  setSign(1)
  def normalClone():this.type = APAInputGCD(l).asInstanceOf[this.type]
  def simplified:APAInputTerm = {
    if(isZero) return APAInputCombination(0)
    val (integers, non_integers)  = APAInputTerm.partitionInteger(l map (_.simplified))
    val result = (Common.gcdlistComplete(integers), non_integers) match {
      case (Some(1), _) => APAInputCombination(1, Nil)
      case (None, k::Nil) => APAInputAbs(k).simplified
      case (None, Nil) =>
        throw new Error("GCD is not defined on an empty set")
      case (None, l) => APAInputGCD(l)
      case (Some(n), Nil) => APAInputAbs(APAInputCombination(n, Nil)).simplified
      case (Some(n), l)   => APAInputGCD(APAInputCombination(n, Nil)::l)
    }
    result.propagateSign(this)
  }
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    APAInputGCD(l map (_.replace(y, t))).simplified.propagateSign(this)
  }
  def input_variables: List[InputVar] = {
    (l flatMap (_.input_variables)).removeDuplicates
  }
}

case class APAInputLCM(l: List[APAInputTerm]) extends APAInputTerm {
  setSign(1)
  def normalClone():this.type = APAInputLCM(l).asInstanceOf[this.type]
  def simplified:APAInputTerm = {
    if(isZero) return APAInputCombination(0)
    val (integers, non_integers)  = APAInputTerm.partitionInteger(l map (_.simplified))
    val result = (Common.lcmlist(integers), non_integers) match {
      case (1, Nil) => APAInputCombination(1)
      case (1, k::Nil) => APAInputAbs(k).simplified
      case (1, k1::k2::l) if k1 == k2 => APAInputLCM(k2::l).simplified
      case (1, l) => APAInputLCM(l)
      case (n, Nil) => APAInputAbs(APAInputCombination(n, Nil)).simplified
      case (n, l) => APAInputLCM(APAInputCombination(n, Nil)::l)
    }
    result.propagateSign(this)
  }
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    APAInputLCM(l map (_.replace(y, t))).simplified.propagateSign(this)
  }
  def input_variables: List[InputVar] = {
    (l flatMap (_.input_variables)).removeDuplicates
  }
}

case class APAInputMod(operand: APAInputTerm, divisor: APAInputTerm) extends APAInputTerm {
  setSign(true, true, false) // >= 0
  if(divisor.can_be_zero) throw new Exception("Error : "+divisor+" can be zero in expression "+this)

  def normalClone():this.type = APAInputMod(operand, divisor).asInstanceOf[this.type]
  def simplified:APAInputTerm = {
    if(isZero) return APAInputCombination(0)
    val result = (operand.simplified, divisor.simplified) match {
      case (APAInputCombination(0, Nil), _) => APAInputCombination(0, Nil)
      case (_, APAInputCombination(1, Nil)) => APAInputCombination(0, Nil)
      case (APAInputCombination(i, Nil), APAInputCombination(j, Nil)) if j != 0 => APAInputCombination(Common.smod(i, j), Nil)
      case (o, d) => APAInputMod(o, d)
    }
    result.propagateSign(this)
  }
  def replace(y: InputVar, t: APAInputTerm):APAInputTerm = {
    APAInputMod(operand.replace(y, t), divisor.replace(y, t)).simplified.propagateSign(this)
  }
  def input_variables: List[InputVar] = {
    (operand.input_variables ++ divisor.input_variables).removeDuplicates
  }
}
