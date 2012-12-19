import synthesis.Definitions._

object SecondsUnique {
  def main(args: Array[String]): Unit = {
    println("Please enter a number of seconds: ")
    val secnum: Int = Console.readInt

    val (hours, hours1, minutes, minutes1, seconds, seconds1) = choose((h: Int, h1 : Int, m : Int, m1 : Int, s: Int, s1 : Int) => (
           h * 3600 + m * 60 + s == secnum &&
           h1 * 3600 + m1 * 60 + s1 == secnum 
        && 0 <= m  && m < 60
        && 0 <= s  && s < 60
        && 0 <= m1  && m1 < 60
        && 0 <= s1  && s1 < 60 
        && (s != s1 || m != m1 || h != h1)
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

    print(secnum + "s = " + hours + "h, " + minutes + "m and " + seconds + "s, but also: ")
    println(hours1 + "h, " + minutes1 + "m and " + seconds1 + "s.")
  }
}
