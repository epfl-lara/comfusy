//	piskac@larapc01:~/guru$ pwd
//	/home/piskac/guru
//	piskac@larapc01:~/guru$ scalac -d bin/ src/guru/synthesis/*.scala
//	piskac@larapc01:~/guru$ scala -cp bin/ guru.synthesis.Main






package guru.synthesis

object Main  {

  def main(args : Array[String]): Unit = {
    guru.synthesis.Examples.runExamples()
  }
}

