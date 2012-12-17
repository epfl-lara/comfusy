package decision


import AST._;
import Primitives._;
import java.util.Calendar;

object Z3Converter {
  abstract sealed class Z3Output;
  case class Z3Failure(e: Exception) extends Z3Output
  case object Unsat extends Z3Output;
  case class Sat(deleteModel: (() => Unit), boolAssignments: (Symbol => Boolean), intAssignments: (Symbol => Int)) extends Z3Output;

  case class IllegalTerm(a: Any) extends Exception(a + " should not be present here");

  val header = "(benchmark X\n :logic QF_LIA \n :status unknown\n"

  /* This converts the formula to SMT string
* format. The task is easier for us because
* We do not have to deal with Division */
  def toSMTBenchmark(form: Formula, intVarsInFormula: List[String], boolVarsInFormula: List[String]): String = {

    def cleanName(frName: String): String = frName.replace("[", "_").replace("]", "_").replace(":", "_")

    def term2string(trm: Term): String = trm match {
      case TermVar(name) => cleanName(name.toString)
      case Lit(IntLit(v)) => v.toString
      case Op(ADD, trmLst) => trmLst.map(term2string(_)).reduceLeft((s1: String, s2: String) => "(+ " + s1 + " " + s2 + ")")
      case Op(SUB, t1 :: t2 :: Nil) => "(- " + term2string(t1) + " " + term2string(t2) + ")"
      case Op(MUL, trmLst) => trmLst.map(term2string(_)).reduceLeft((s1: String, s2: String) => "(* " + s1 + " " + s2 + ")")
      case Op(ITE(f), t1 :: t2 :: Nil) => "(ite " + form2string(f) + " " + term2string(t1) + " " + term2string(t2) + ")"
      case Op(MIN, t1 :: t2 :: rest) => {
        val subExpr = term2string(Op(MIN, t2 :: rest))
        val thisExpr = term2string(t1)
        "(ite " + "(< " + thisExpr + " " + subExpr + ") " + thisExpr + " " + subExpr + ")"
      }
      case Op(MIN, t1 :: Nil) => term2string(t1)
      case Op(MAX, t1 :: t2 :: rest) => {
        val subExpr = term2string(Op(MAX, t2 :: rest))
        val thisExpr = term2string(t1)
        "(ite " + "(> " + thisExpr + " " + subExpr + ") " + thisExpr + " " + subExpr + ")"
      }
      case Op(MAX, t1 :: Nil) => term2string(t1)
      case _ => throw (new IllegalTerm(trm))
    }

    def op2string(op: IntOperand, t1: Term, t2: Term): String = op match {
      case LT => "(< " + term2string(t1) + " " + term2string(t2) + ")"
      case LE => "(<= " + term2string(t1) + " " + term2string(t2) + ")"
      case EQ => "(= " + term2string(t1) + " " + term2string(t2) + ")"
      case NE => "(distinct " + term2string(t1) + " " + term2string(t2) + ")"
      case GT => "(> " + term2string(t1) + " " + term2string(t2) + ")"
      case GE => "(>= " + term2string(t1) + " " + term2string(t2) + ")"
    }

    def form2string(f: Formula): String = f match {
      case True => "true"
      case False => "false"
      case PropVar(v) => cleanName(v.toString)
      case And(fs) => "(and " + fs.map(form2string(_)).mkString(" ") + ")"
      case Or(fs) => "(or " + fs.map(form2string(_)).mkString(" ") + ")";
      case Not(form) => "(not " + form2string(form) + ")"
      case Predicate(op: IntLogical, t1 :: t2 :: Nil) => op2string(op, t1, t2)
      case _ => throw (new IllegalTerm(f))
    }

    val formulaString = form2string(form)
    var str = header
    if (!intVarsInFormula.isEmpty || !boolVarsInFormula.isEmpty) {
      str = str + ":extrafuns ( "
      intVarsInFormula.foreach(v => str = str + "(" + cleanName(v) + " Int) ")
      boolVarsInFormula.foreach(v => str = str + "(" + cleanName(v) + " Bool) ")
      str = str + ")\n";
    }

    str = str + " :formula \n" + formulaString + "\n)";
    str
  }

  /* Code on the lines of the code in Arithmetic.scala
* The mappings for the boolean and the integer variables are returned separately
* TODO: WARNING: It might be the case that some variables might be left unassigned
* in the model provided. The value of these parameters does not change the
* truth value of the formula, in that case. */
  def isSat(form: Formula): Z3Output = {
    try {
      val intVarsInForm = ASTUtil.intvars(form).toList.map(_.name.toString)
      val boolVarsInForm = ASTUtil.propvars(form).toList.map(_.name.toString)
      val smt = toSMTBenchmark(form, intVarsInForm, boolVarsInForm)
      //println(smt)

      val startTime = Calendar.getInstance().getTimeInMillis();
      val process = java.lang.Runtime.getRuntime.exec("z3 -smt -in")
      val out = new java.io.PrintStream(process.getOutputStream)
      out.println(smt)
      out.flush
      out.close
      val in = new java.io.BufferedReader(new java.io.InputStreamReader(process.getInputStream))
      var line: String = in.readLine
      var lines: List[String] = Nil
      while (line != null) {
        lines = line :: lines
        line = in.readLine
      }
      val runningTime = Calendar.getInstance().getTimeInMillis() - startTime;
      lines = lines.reverse

      var assignmentsInt = Map.empty[String, Int]
      var assignmentsBool = Map.empty[String, Boolean]
      var status: Option[Boolean] = None

      for (val l <- lines) {
        if (l.contains(" -> ")) {
          val spl = l.split(" -> ")
          if (intVarsInForm.contains(spl(0)))
            assignmentsInt = assignmentsInt + (spl(0) -> spl(1).toInt)
          if (boolVarsInForm.contains(spl(0)))
            assignmentsBool = assignmentsBool + (spl(0) -> (spl(1) == "true"))
        } else if (l.contains("unsat")) {
          status = Some(false)
        } else if (l == "sat") {
          status = Some(true)
        }
      }
      status match {
        case Some(st) => if (st == true) Sat({() => ()}, (x => assignmentsBool.getOrElse(x.name, false)), (x => assignmentsInt.getOrElse(x.name, 0))) else Unsat
        case None =>
          Console.err.println("Z3 returned an error.")
          Z3Failure(new IllegalTerm(lines))
      }
    } catch {
      case (e: java.io.IOException) => {
        Console.err.println("Warning: Cannot execute Z3. Is the executable in the path?.\n")
        Z3Failure(e)
      }
    }
  }


  def runAndPrint(paForm: Formula) = isSat(paForm) match {
    case Sat(t, _, _) => println("Formula satisfiable"); t()
    case Unsat => println("Formula unsatisfiable")
    case Z3Failure(e) => println("Z3 not executed.")
  }
}
/*
object Z3ConverterTester {
  def main(args: Array[String]) = {
    val a = Symbol("a")
    val b = Symbol("b")
    val c = Symbol("c")
    val d = Lit(IntLit(3))
    val p = PropVar(Symbol.beta(1, TermVar(Symbol.freshSet)))

    val form = (a * d - c === 10) && (c === Op(MIN, TermVar(a)::(b+1)::d::Nil)) && b === Op(MAX, (a+1)::TermVar(c)::Nil)
    println("Formula = ");
    form.print;
    println("Bool vars = " + ASTUtil.propvars(form));
    println("Z3 formula = " + Z3Converter.toSMTBenchmark(form, List(a, b, c).map(_.toString), Nil))
    println("Z3 result = " + Z3Converter.isSat(form))
  }
}
*/
