import synthesis.Definitions._

object SecondsToTime {
  def main(args: Array[String]): Unit = {
    println("Please enter a number of seconds: ")
    val secnum: Int = Console.readInt

    val (hours, minutes, seconds) = choose((h: Int, m: Int, s: Int) => (
           h * 3600 + m * 60 + s == secnum
        && 0 <= m
        && m < 60
        && 0 <= s
        && s < 60
      ) )


    // should be rewritten into something looking vaguely like this:
    // val (hours, minutes, seconds) = {
    //   var fresh_h: Int = 0
    //   var fresh_m: Int = 0
    //   var fresh_s: Int = 0

    //   fresh_h = (secnum / 3600)
    //   fresh_m = (secnum % 3600) / 60
    //   fresh_s = (secnum % 60)

    //   (fresh_h, fresh_m, fresh_s)
    // }

    println(secnum + "s = " + hours + "h, " + minutes + "m and " + seconds + "s.")
  }
}

