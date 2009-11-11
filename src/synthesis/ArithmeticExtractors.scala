package synthesis

/** Helper extractors to pull out these pesky arithmetic expressions. */
trait ArithmeticExtractors {
  self: ChooseTransformer =>
  import global._
  import global.definitions._

  object ExTrueLiteral {
    def unapply(tree: Tree): Boolean = tree match {
      case Literal(Constant(true)) => true
      case _ => false
    }
  }

  object ExFalseLiteral {
    def unapply(tree: Tree): Boolean = tree match {
      case Literal(Constant(false)) => true
      case _ => false
    }
  }

  object ExAnd {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_and) =>
        Some((lhs,rhs))
      case _ => None
    }
  }

  object ExOr {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_or) =>
        Some((lhs,rhs))
      case _ => None
    }
  }

  object ExNot {
    def unapply(tree: Tree): Option[Tree] = tree match {
      case Select(t, n) if (n == nme.UNARY_!) => Some(t)
      case _ => None
    }
  }

  object ExEquals {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.EQ) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExNotEquals {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.NE) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExLessThan {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.LT) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExLessEqThan {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.LE) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExGreaterThan {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.GT) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExGreaterEqThan {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.GE) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExIntLiteral {
    def unapply(tree: Tree): Option[Int] = tree match {
      case Literal(c @ Constant(i)) if c.tpe == IntClass.tpe => Some(c.intValue)
      case _ => None
    }
  }

  object ExIntIdentifier {
    def unapply(tree: Tree): Option[Ident] = tree match {
      case i: Ident if i.symbol.tpe == IntClass.tpe => Some(i)
      case _ => None
    }
  }

  object ExPlus {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.ADD) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExMinus {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.SUB) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExTimes {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.MUL) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExDiv {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.DIV) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExModulo {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.MOD) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExNeg {
    def unapply(tree: Tree): Option[Tree] = tree match {
      case Select(t, n) if (n == nme.UNARY_-) => Some(t)
      case _ => None
    }
  }
}
