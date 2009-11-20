import synthesis.Definitions._

object IntsAboutPartitions {
  def main(args: Array[String]): Unit = {
    val b1 = Set("my", "little", "cat")
    val b2 = Set("cat", "likes", "mice", "but", "not", "rice")
    val k11:Int = (b2 intersect b1).size
    val k01:Int = (b2 -- b1).size
    val k10:Int = (b1 -- b2).size
    val k00:Int = 10000 // infinity
    val (h000,h001,h010,h011,h100,h101,h110,h111) = choose ((h000:Int,h001:Int,h010:Int,h011:Int,h100:Int,h101:Int,h110:Int,h111:Int) =>
      (h111:Int) + (h110:Int) = (k11:Int) &&
      h011 + h010 = k01 &&
      h101 + h100 = k10 &&
      h001 + h000 = k00 &&
      (2:Int) <= h111 + h101 + h011 + h001 &&
      h011 + h001 = 0 &&
      h100 + h101 = 0)
    println((h000,h001,h010,h011,h100,h101,h110,h111))
  }
}
