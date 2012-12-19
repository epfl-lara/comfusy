import synthesis.Definitions._

object IntsAboutPartitions {
  def main(args: Array[String]): Unit = {
    val b1 = Set("my", "little", "cat",  "cooker")
    val b2 = Set("cat", "likes", "mice", "but", "not", "rice")
    val k11:Int = (b2 intersect b1).size
    val k01:Int = (b2 -- b1).size
    val k10:Int = (b1 -- b2).size
    val k00:Int = 10000 // infinity

    println(k00 + " " + k01 + " " + k10 + " " + k11)

    val (h000,h001,h010,h011,h100,h101,h110,h111) = choose ((h000:Int,h001:Int,h010:Int,h011:Int,h100:Int,h101:Int,h110:Int,h111:Int) =>
      h111 + h110 == k11 &&
      h011 + h010 == k01 &&
      h101 + h100 == k10 &&
      h001 + h000 == k00 &&
      2 <= h111 + h101 + h011 + h001 &&
      h011 + h001 == 0 &&
      h101 + h001 == 0 &&
      h000 >= 0 &&
      h001 >= 0 &&
      h010 >= 0 &&
      h011 >= 0 &&
      h100 >= 0 &&
      h101 >= 0 &&
      h110 >= 0 &&
      h111 >= 0 
    )
    println((h000,h001,h010,h011,h100,h101,h110,h111))
  }
  
}
