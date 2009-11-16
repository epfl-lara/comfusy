package synthesis

object Common {
  
  def bezout(e: Int, a : Int*): List[Int] = bezout(e, a.toList)
  
  // Finds a vector x such that x.a + e is 0 if this is possible.
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
                (a_indexed map { case (i, c) => if(i==index) -e/sign else 0 })
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
                
                val new_e = (e + Math.abs(min_coef) * (smod(e, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                val new_a = Math.abs(min_coef)::(a map {
                  case k => (k + Math.abs(min_coef) * (smod(k, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                })
                // the coefficient at index 'index+1' is now 0, so it will be removed.
                
                // Now, there is at least one zero in new_a
                bezout(new_e, new_a) match {
                  case Nil => throw new Error("Should not happen, the size of the input and output are the same")
                  case q@(w::l) =>
                    l.splitAt(index) match {
                    // The coefficient at index 'index' of l should be zero, we replace it by its assignment
                    case (left, 0::right) =>
                      val solution_a = scalarProduct(a_assign, q)
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

  def enumerate[A](a: List[A]):List[(Int, A)] = (a.indices zip a)
  
  // a is an indexed list
  def replaceElementAtIndexByCoef(a: List[(Int, Int)], index: Int, coef: Int) = a map { _ match {
        case (i, c) =>  if(i == index) coef else c
    } }
  
  // a is an indexed list
  def replaceEverythingByCoef1ExceptCoef2AtIndex(a: List[(Int, Int)], coef1:Int, coef2: Int,index: Int): List[Int] =
    a map { _ match {
        case (i, c) if i == index => coef2
        case _ => coef1
      }
    }
  
  // a is an indexed list
  def replaceEverythingByZeroExcept1AtIndex(a: List[(Int, Int)], index: Int): List[Int] =
    replaceEverythingByCoef1ExceptCoef2AtIndex(a, 0, 1, index)

  // a is an indexed list
  def putCoef1AtIndex1andCoef2AtIndex2(a: List[(Int, Int)], coef1: Int, index1: Int, coef2: Int, index2: Int ):List[Int] = {
    a map { _ match {
        case (i, c) =>
          if(i == index1) coef1
          else if(i==index2) coef2
          else 0
      }
    }
  }
  
  //insertPreviousZeros([a, b, 0, c, 0, d], [x, y, z, w]) = [x, y, 0, z, 0, d]
  def insertPreviousZeros(list_with_zeros: List[Int], list_to_complete: List[Int]) :List[Int] = {
    val (_, result) = list_with_zeros.foldLeft((list_to_complete, Nil: List[Int]))( (_, _) match {
      case ((l, result), 0)    => (l, 0::result)
      case ((a::q, result), _) => (q, a::result)
    })
    result.reverse
  }
  
  def scalarProduct(a: List[Int], b:List[Int]): Int = {
    (a zip b).foldLeft(0){case (result, (e_a, e_b)) => result + e_a * e_b}
  }
  
  def bezoutWithBase(e: Int, a : Int*): List[List[Int]] = bezoutWithBase(e, a.toList)
  // If size(a) == n, finds a matrix x of size n x n
  // such that (1, k1, k2, .. kn-1).x.a + e = 0 if this is possible,
  // and x describes all integer solutions of this equation. Rank(x) = n-1
  // Output representation : it's the list of rows.
  //                               n          n     n
  def bezoutWithBase(e: Int, a: List[Int]): (List[List[Int]]) = {
    a match {
      case Nil => Nil
      case 0::Nil => ((0::Nil)::Nil)
      case k::Nil => (((-e + smod(e, k))/k) :: Nil) :: Nil
      case a =>
        val a_indexed:List[(Int, Int)] = enumerate(a)
        (a_indexed find (_._2 == 0)) match {
          case Some((index, element)) =>
          // Takes the result when removing the zeros, then inserts some zeros.
            val a_filtered = a remove ( _ == 0 )
            val solution = bezoutWithBase(e, a_filtered)
            val (_, solution_completed) = a_indexed.foldLeft((solution, Nil:List[List[Int]]))((_,_) match { 
              case ((q, l), (i, 0))    => (q, replaceEverythingByZeroExcept1AtIndex(a_indexed, i)::l)
              case ((Nil, l), (i, k))  => (Nil, l) // This should not happen, as we have many zeroes.
              case ((b::q, l), (i, k)) => (q, insertPreviousZeros(a, b)::l)
            })
            // For each zero in a_indexed, add a new vector where 1 is at this position and it's zero everywhere else.
            val new_vectors = a_indexed flatMap {
              case (index, 0) => List(replaceEverythingByZeroExcept1AtIndex(a_indexed, index))
              case t => Nil
            }
            solution_completed.reverse
          case None =>
            (a_indexed find {case a => Math.abs(a._2) == 1}) match {
              case Some((index, element)) =>
                // This is easy, like solving 4x+y+45z=30, just say that y=30 and other are zero
                // For the vectors, just take the other variables as themselves.
                val neg_sign = if(element > 0) -1 else 1
                replaceEverythingByCoef1ExceptCoef2AtIndex(a_indexed, 0, neg_sign*e, index) ::
                (a_indexed flatMap ( _ match {
                  case (i, c) =>
                    if(i == index)
                      Nil
                    else
                      List(putCoef1AtIndex1andCoef2AtIndex2(a_indexed, 1, i, neg_sign*c, index))
                }))
              case None =>
                    val (index, min_coef) = a_indexed reduceLeft {
                  (_, _) match {
                    case (t1@(i, ci), t2@(j, cj)) => if(Math.abs(ci) < Math.abs(cj)) t1 else t2
                  }}
                val min_coef_sign = if(min_coef > 0) 1 else -1
                val min_coef_sign2 = if(min_coef > 0) -1 else 1
                val abs_min_coef_plus_1 = Math.abs(min_coef) + 1
                val e_assign = smod(e, abs_min_coef_plus_1)
                val a_assign = abs_min_coef_plus_1 :: (a map {case k => smod(k, abs_min_coef_plus_1)})
                // the coefficient at index 'index+1' is now 1 or -1.
                
                val new_e = (e + Math.abs(min_coef) * (smod(e, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                val new_a = Math.abs(min_coef)::(a map {
                  case k => (k + Math.abs(min_coef) * (smod(k, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                })
                // the coefficient at index 'index+1' is now 0, so it will be removed.
                
                // Now, there is at least one zero in new_a
                bezoutWithBase(new_e, new_a) match {
                  case Nil => throw new Error("Should not happen as the input was not empty")
                  case v =>
                    val v_reduced = enumerate(v) flatMap {
                      case (i, Nil) => throw new Error("Should not happen as the input was not empty")
                      case (i, vs@(a::q)) =>
                        if(i == index +1) // We drop the line indicated by index
                          Nil
                        else {
                          val vs_replaced = replaceElementAtIndexByCoef(enumerate(vs), index+1, 0)
                          if(i==0) {
                            val new_element = (e_assign+scalarProduct(a_assign, vs_replaced)) * min_coef_sign
                            List(replaceElementAtIndexByCoef(enumerate(q), index, new_element))
                          } else {
                            val new_element = (scalarProduct(a_assign, vs_replaced)) * min_coef_sign
                            List(replaceElementAtIndexByCoef(enumerate(q), index, new_element))
                          }
                        }
                    }
                    v_reduced
                  }
                }
            }
        }
    }
  
  def smod(x:Int, m_signed:Int) = {
    val m = Math.abs(m_signed)
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
