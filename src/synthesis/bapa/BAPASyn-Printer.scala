package guru.synthesis


object Printer {

  def print_variables(s: String, l: List[String]): Unit = {
    if (!l.isEmpty) {
      l.foreach(v => {
        val s1 = s + v + "."
        Console.print(s1)
      })
    }
  }

  def print_Int(i: PAInt): Unit = i match {
    case IntVar(v) => Console.print(v)
    case IntConst(c) => Console.print(c)
    case Plus(i1, i2) => {
      print_Int(i1)
      Console.print(" + ")
      print_Int(i2)
    }
    case Times(c, i1) => {
      Console.print(c + "*")
      print_Int(i1)
    }
    case Card(s) => {
      Console.print("| ")
      print_Set(s)
      print(" |")
    }
  }

  def print_Set(s: BASet): Unit = s match {
    case SetVar(v) => Console.print(v)
    case EmptySet => Console.print("EMPTY SET")
    case UnivSet => Console.print("UNIVERSAL SET")
    case Union(s1, s2) => {
      print_Set(s1)
      Console.print(" UNION ")
      print_Set(s2)
    }
    case Intersec(s1, s2) => {
      print_Set(s1)
      Console.print(" INTERSEC ")
      print_Set(s2)
    }
    case Compl(s1) => {
      Console.print("( ")
      print_Set(s1)
      print(" )^c ")
    }
  }


  def print_BAPAAtom(a: Atom): Unit = a match {
    case SetEqual(s1, s2) => {
      print_Set(s1)
      Console.print(" = ")
      print_Set(s2)
    }
    case SetSubset(s1, s2) => {
      print_Set(s1)
      Console.print(" SUBSET ")
      print_Set(s2)
    }
    case IntEqual(i1, i2) => {
      print_Int(i1)
      Console.print(" = ")
      print_Int(i2)
    }
    case IntLessEqual(i1, i2) => {
      print_Int(i1)
      Console.print(" =< ")
      print_Int(i2)
    }
    case IntDivides(c, i) => {
      Console.print(c + " | ")
      print_Int(i)
    }
  }

  def print_BAPAFormula(f: Formula): Unit = f match {
    case And(f1, f2) => {
      Console.print(" ( ")
      print_BAPAFormula(f1)
      print(" ) AND ( ")
      print_BAPAFormula(f2)
      print(" ) ")
    }
    case Or(f1, f2) => {
      Console.print(" ( ")
      print_BAPAFormula(f1)
      print(" ) OR ( ")
      print_BAPAFormula(f2)
      print(" ) ")
    }
    case Not(f1)  => {
      Console.print(" NOT ( ")
      print_BAPAFormula(f1)
      print(" ) ")
    }
    case FAtom(a)  => print_BAPAAtom(a)
  }



  def print_Task(t: Task): Unit = t match {
    case Task(x, y, k, l, f) => {
      print_variables("FORALL ", x)
      print_variables("FORALL ", k)
      print_variables("EXISTS ", y)
      print_variables("EXISTS ", l)
      print_BAPAFormula(f)
      println(" ")
    }
  }
}

