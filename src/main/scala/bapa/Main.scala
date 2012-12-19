//	piskac@larapc01:~/guru$ pwd
//	/home/piskac/guru
//	piskac@larapc01:~/guru$ scalac -d bin/ synthesis-plugin/src/synthesis/bapa/*.scala  synthesis-plugin/src/synthesis/Arithmetic.scala
//	piskac@larapc01:~/guru$ scala -cp bin/ synthesis.bapa.Main




package synthesis.bapa

object Main  {

  def main(args : Array[String]): Unit = {
    synthesis.bapa.Examples.runExamples()
  }
}

