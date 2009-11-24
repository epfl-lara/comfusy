package synthesis

object PASynthesisExamples {
  import PASynthesis._
  def O(name: String) = PASynthesis.OutputVar(name)
  def I(name: String) = PASynthesis.InputVar(name)
  implicit def OutputVarToPACombination(o: OutputVar):PACombination = PACombination(o)
  implicit def InputVarToPACombination(i: InputVar):PACombination = PACombination(i)
  implicit def IntegerToPACombination(k: Int):PACombination = PACombination(k)

  val x = O("x")
  val x1 = O("x1")
  val y = O("y")
  val y1 = O("y1")
  val z = O("z")
  
  val b = I("b")
  val c = I("c")
  val d = I("d")

  def main(args : Array[String]) : Unit = {
    hourMinutSecondExample()
    balancedProblem()
    dividesExample()
    HourMinutSecondUnique()
  }
  
  def hourMinutSecondExample() {
    val seconds = I("seconds")
    val s = O("s")
    val m = O("m")
    val h = O("h")
    val condition = (
         seconds === s + (m * 60) + (h*3600)
      && s >= 0 && s < 60
      && m >= 0 && m < 60
    )
    val solution = PASynthesis.solve("getHourMinutSeconds", condition)
    println(solution._1)
    println(solution._2)
  }
  def HourMinutSecondUnique() {
    val seconds = O("seconds")
    val s1 = O("s1")
    val m1 = O("m1")
    val h1 = O("h1")
    val s2 = O("s2")
    val m2 = O("m2")
    val h2 = O("h2")
    val condition = seconds === s1 + (m1 * 60) + (h1*3600) && seconds === s2 + (m2 * 60) + (h2*3600) &&
      s1 >= 0 && s1 < 60 &&
      m1 >= 0 && m1 <= 60 &&
      s2 >= 0 && s2 < 60 &&
      m2 >= 0 && m2 <= 60 &&
      ((s1 > s2) || (s2 > s1) || (m1 > m2) || (m2 > m1) || (h1 > h2) || (h2 > h1)) 
    
    val solution = PASynthesis.solve("HourMinutSecondUnique", condition)
    println(solution._1)
    println(solution._2)
  }
  def balancedProblem() {
    val weight = I("weight")
    val w1 = O("w1")
    val w2 = O("w2")
    val w3 = O("w3")
    val c1 = PAEqualZero(PACombination(0, (-1, weight)::Nil, (1, w1)::(3, w2)::(9, w3)::Nil))
    val c2 = PAGreaterEqZero(PACombination(1, Nil, (1, w1)::Nil))
    val c3 = PAGreaterEqZero(PACombination(1, Nil, (-1, w1)::Nil))
    val c4 = PAGreaterEqZero(PACombination(1, Nil, (1, w2)::Nil))
    val c5 = PAGreaterEqZero(PACombination(1, Nil, (-1, w2)::Nil))
    val c6 = PAGreaterEqZero(PACombination(1, Nil, (1, w3)::Nil))
    val c7 = PAGreaterEqZero(PACombination(1, Nil, (-1, w3)::Nil))
    val solution = PASynthesis.solve("getWeights", c1::c2::c3::c4::c5::c6::c7::Nil)
    println(solution._1)
    println(solution._2)
  }
  
  def dividesExample() {
    val pac1 = PADivides(5, PACombination(b)+PACombination(y))
    val pac2 = PADivides(7, PACombination(c)+PACombination(y))
    val solution = PASynthesis.solve("divides5And7", pac1::pac2::Nil)
    println(solution._1)
    println(solution._2)
  }
}
