package synthesis

object Common {
  
  def bezout(e: Int, a : Int*): List[Int] = bezout(e, a.toList)
  
  // Finds a vector x such that x.a + e is the closest as possible to 0, and postive if there are two possibilities.
  def bezout(e: Int, a : List[Int]):List[Int] = {
    a match {
      case Nil => Nil
      case 0::Nil => 0::Nil
      case k::Nil => ((-e + smod(e, k))/k) :: Nil
      case a =>
        val a_indexed:List[(Int, Int)] = (a.indices zip a)
        (a_indexed find (_._2 == 0)) match {
          case Some((index, element)) =>
          // Takes the result when removing the zeros, then inserts some zeros.
            val a_filtered = a remove (_==0)
            val a_filtered_solved = bezout(e, a_filtered )
            val (_, a_solved) = a.foldLeft((a_filtered_solved, Nil:List[Int]))((_,_) match { 
              case ((q, l), 0)    => (q, 0::l)
              case ((Nil, l), k)  => (Nil, l) // This should not happen, as we have many zeroes.
              case ((a::q, l), k) => (q, a::l)
            })
            a_solved.reverse
          case None =>
            (a_indexed find {case a => Math.abs(a._2) == 1}) match {
              case Some((index, element)) => // This is easy, like solving 4x+y+45z=30, just say that y=30 and other are zero
                val sign = if(element > 0) 1 else -1
                (a_indexed map { case (i, c) => if(i==index) -e else 0 })
              case None =>
                    val (index, min_coef) = a_indexed reduceLeft {
                  (_, _) match {
                    case (t1@(i, ci), t2@(j, cj)) => if(Math.abs(ci) < Math.abs(cj)) t1 else t2
                  }}
                val min_coef_sign = if(min_coef > 0) 1 else -1
                val abs_min_coef_plus_1 = Math.abs(min_coef) + 1
                val e_assign = smod(e, abs_min_coef_plus_1)
                val a_assign = abs_min_coef_plus_1 :: (a map {case k => smod(k, abs_min_coef_plus_1)})
                // the coefficient at index 'index+1' is now 1 or -1.
                
                val new_e = (e + min_coef * (smod(e, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                val new_a = min_coef::(a map {
                  case k => (k + min_coef * (smod(k, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                })
                // the coefficient at index 'index+1' is now 0, so it will be removed.
                
                // Now, there is at least one zero in new_a
                bezout(new_e, new_a) match {
                  case Nil => throw new Error("Should not happen, the size of the input and output are the same")
                  case q@(w::l) =>
                    l.splitAt(index) match {
                    // The coefficient at index 'index' of l should be zero, we replace it by its assignment
                    case (left, 0::right) =>
                      val solution_a = ((a_assign zip q).foldLeft(0){ case (result, (k, l)) => result + k*l})
                      val solution = (solution_a + e_assign)*(min_coef_sign)
                      val result = left++(solution::right)
                      result
                    case (l, m) => throw new Error("The list "+l+" should have 0 at index "+index+" but this is not the case")
                  }
                }
            }
        }
    }
    
  }
  
  
  def smod(x:Int, m:Int) = {
    val c = x % m
    if(c >= (m+1)/2)
      c - m
    else if(c < -m/2)
      c + m
    else c
  }
  
  // Computes the GCD between two numbers
  // Unsafe if y = -2^31
  def gcd(x:Int, y:Int): Int = {
    if (x==0) Math.abs(y)
    else if (x<0) gcd(-x, y)
    else if (y<0) gcd(x, -y)
    else gcd(y%x, x)
  }
  // Computes the LCM between two numbers
  
  def lcm(x: Int, y: Int): Int = {
    if(x < 0) lcm(-x, y)
    else if(y < 0) lcm(x, -y)
    else x * y / gcd(x, y)
  }
  // Computes the LCM over a list  of numbers
  def lcmlist(l:List[Int]):Int = l match {
    case Nil => 1
    case a::Nil => a
    case (a::b::q) => lcmlist(lcm(a,b)::q)
  }
  // Computes the GCD over a list  of numbers
  def gcdlist(l:List[Int]):Int = l match {
    case Nil => 1
    case 0::Nil => 1
    case a::Nil => lcm(a, 1)
    case (a::b::q) => gcdlist(gcd(a,b)::q)
  }
}
