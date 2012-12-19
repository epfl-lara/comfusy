import synthesis.Definitions._

object ChristmasSong {
    def main(args : Array[String]) : Unit = {
        println("eLines (6) ?")
        val eLines: Int = Console.readInt
        println("iLines (2) ?")
        val iLines: Int = Console.readInt
        println("iSyls (5) ?")
        val iSyls: Int  = Console.readInt
        println("nSyls (952) ?")
        val nSyls: Int = Console.readInt

        val (line7, line8, nsLines, nLines, tLines, _) =
            choose((line7: Int, line8: Int, nsLines: Int, nLines: Int, tLines: Int, tLinesFact: Int) => (
                   tLines == eLines + nLines
                && nLines == iLines + nsLines
                && nLines == line7 + line8
                && nSyls + iSyls == 7 * line7 + 8 * line8
                && tLines == 4 * tLinesFact // expresses (4 | tLines)
                && line8 >= 0
                && line7 >= 0
                && tLines >= 0
            ))

        println("line7 : " + line7)
        println("line8 : " + line8)
        println("nsLines : " + nsLines)
        println("nLines : " + nLines)
        println("tLines : " + tLines)
    }
}
