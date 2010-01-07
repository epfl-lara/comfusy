package synthesis

/**********************
  *  Sign abstraction  *
  **********************/

// dummy
object APAAbstractions

object SignAbstraction { // This is an integer abstraction.
  def addSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    ASign((a.pos || b.pos), (a.nul && b.nul) || (a.pos && b.neg) || (b.pos && a.neg), (a.neg || b.neg))
  }
  def addSign(l: List[SignAbstraction]):ASign = {
    l.foldLeft(ASign(false, true, false))(addSign(_, _))
  }
  def multSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    val result = ASign((a.pos && b.pos) || (a.neg && b.neg), (a.nul || b.nul), (a.pos && b.neg) || (a.neg && b.pos))
    result
  }
  def multSign(l: List[SignAbstraction]):ASign = {
      l.foldLeft(ASign(true, false, false))(multSign(_, _))
  }
  def divSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    if(b.nul)
      throw new Exception("Error : "+b+" can be zero")
    ASign((a.pos && b.pos) || (a.neg && b.neg), (a.pos || a.neg || a.nul) && (b.pos || b.neg || b.nul), (a.pos && b.neg) || (a.neg && b.pos))
  }
  def oppSign(a: SignAbstraction):ASign = {
    ASign(a.neg, a.nul, a.pos)
  }
  def absSign(a: SignAbstraction):ASign = {
    ASign(a.neg || a.pos, a.nul, false)
  }
  def number(i: Int):ASign = {
    ASign(i > 0, i == 0, i < 0)
  }
  def linearCombinationSign(i: Int, l: List[(Int, SignAbstraction)]):ASign = {
    val l_sign = l map { case (i, sa) => multSign(number(i), sa)}
    addSign(number(i)::l_sign)
  }
  def mergeSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    ASign(a.pos && b.pos, a.nul && b.nul, a.neg && b.neg)
  }
}

trait SignAbstraction {
  // Simple >0, =0 and <0 abstraction
  private var private_pos: Boolean = true
  private var private_nul: Boolean = true
  private var private_neg: Boolean = true
  def pos:Boolean = private_pos
  def nul:Boolean = private_nul
  def neg:Boolean = private_neg
  
  def normalClone():this.type
  
  private def cloneWithSign(a: SignAbstraction):this.type = {
    this.cloneWithSign(a.pos, a.nul, a.neg)
  }
  private def cloneWithSign(pos_ : Boolean, nul_ : Boolean, neg_ : Boolean):this.type = {
    val result = normalClone().asInstanceOf[SignAbstraction]
    result.setSign(pos_, nul_, neg_)
    result.asInstanceOf[this.type]
  }

  protected def setSign(pos_ :Boolean, nul_ :Boolean, neg_ :Boolean) = {
    private_pos = pos_
    private_nul = nul_
    private_neg = neg_
  }
  protected def setSign(i: Int) = {
    private_pos = i > 0
    private_nul = i == 0
    private_neg = i < 0
  }
  protected def setSign(i: SignAbstraction) = {
    private_pos = i.pos
    private_nul = i.nul
    private_neg = i.neg
  }
  
  def isPositive() = pos && !neg && !nul
  def isNegative() = !pos && neg && !nul
  def isPositiveZero() = (pos || nul) && !neg
  def isNotPositiveZero() = !pos && !nul
  def isNegativeZero() = (neg || nul) && !pos
  def isNotNegativeZero() = !neg && !nul
  def isNotPositive() = !pos
  def isNotNegative() = !neg
  def isZero() = nul && !pos && !neg
  def isNotZero() = !nul
  def isNotDefined() = !pos && !neg && !nul
  
  def assumeSign(i: Int):this.type = {
    propagateSign(ASign(i > 0, i == 0, i < 0))
  }
  def assumeZero():this.type = {
    assumeSign(0)
  }
  def assumePositive():this.type = {
    assumeSign(1)
  }
  def assumeNegative():this.type = {
    assumeSign(-1)
  }
  def assumePositiveZero():this.type = {
    propagateSign(ASign(true, true, false))
  }
  def assumeNegativeZero():this.type = {
    propagateSign(ASign(false, true, true))
  }
  def assumeNotZero():this.type = {
    propagateSign(ASign(true, false, true))
  }
  def assumeSign(i: SignAbstraction):this.type = {
    propagateSign(ASign(i.pos, i.nul, i.neg))
  }
  def assumeNotzerobility(i: SignAbstraction):this.type = { // Useful in products : if a*b is not null, then a and b are not null.
    propagateSign(ASign(true, i.nul, true))
  }
  protected def propagateSign_internal(i: SignAbstraction):this.type = {
    cloneWithSign(pos && i.pos, nul && i.nul, neg && i.neg)
  }
  def propagateSign(i: SignAbstraction):this.type = { // This method can be overriden
    propagateSign_internal(i)
  }
}
case class ASign(pos_ : Boolean, nul_ : Boolean, neg_ : Boolean) extends SignAbstraction {
  setSign(pos_, nul_, neg_)
  def normalClone():this.type = ASign(pos_, nul_, neg_).asInstanceOf[this.type]
}
case class PositiveZeroSign() extends SignAbstraction {
  setSign(true, true, false)
  def normalClone():this.type = PositiveZeroSign().asInstanceOf[this.type]
}

/*****************************
  *  Coefficient abstraction  *
  *****************************/

trait CoefficientAbstraction {
  // Simple >0, =0 and <0 abstraction
  private var p_allCoefficientsAreNull:    Boolean = false
  private var p_notAllCoefficientsAreNull: Boolean = false
  def allCoefficientsAreNull    =  p_allCoefficientsAreNull
  def notAllCoefficientsAreNull =  p_notAllCoefficientsAreNull
  
  def normalClone():this.type
    
  def cloneWithCoefficientAbstraction(c: CoefficientAbstraction):this.type = {
    this.cloneWithCoefficientAbstraction(c.allCoefficientsAreNull, c.notAllCoefficientsAreNull)
  }
  def cloneWithCoefficientAbstraction(allCoefficientsAreNull_ : Boolean, notAllCoefficientsAreNull_ : Boolean):this.type = {
    val result = normalClone().asInstanceOf[CoefficientAbstraction]
    result.setCoefficients(allCoefficientsAreNull_, notAllCoefficientsAreNull_)
    result.asInstanceOf[this.type]
  }
  
  private def setCoefficients(a: Boolean, n: Boolean) = {
    p_allCoefficientsAreNull = a
    p_notAllCoefficientsAreNull = n
  }
  
  def assumeAllCoefficientsAreNull : this.type = {
    cloneWithCoefficientAbstraction(true, false)
  }
  def assumeNotAllCoefficientsAreNull : this.type = {
    cloneWithCoefficientAbstraction(false, true)
  }
  protected def setNotAllCoefficientsAreNul() = {
    setCoefficients(false, true)
  }
  protected def setNoCoefficients() = {
    setCoefficients(true, true)
  }
  def propagateCoefficientAbstraction(o : CoefficientAbstraction):this.type = {
    cloneWithCoefficientAbstraction(allCoefficientsAreNull    || o.allCoefficientsAreNull,
                                    notAllCoefficientsAreNull || o.notAllCoefficientsAreNull)
  }
  def addCoefficientAbstraction(o: CoefficientAbstraction):this.type = {
    if(allCoefficientsAreNull && o.allCoefficientsAreNull) {
      assumeAllCoefficientsAreNull
    } else this
  }
  def multCoefficientAbstraction(o: CoefficientAbstraction, i: Int):this.type = {
    if(i==0) {
      assumeAllCoefficientsAreNull
    } else {
      propagateCoefficientAbstraction(o)
    }
  }
}
