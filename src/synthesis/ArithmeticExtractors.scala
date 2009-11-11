package synthesis

/** Helper extractors to pull out these pesky arithmetic expressions. */
trait ArithmeticExtractors {
  self: ChooseTransformer =>
  import global._
  import global.definitions._

  object ExIntLiteral {
    def unapply(tree: Tree): Option[Int] = tree match {
      case Literal(c @ Constant(i)) if c.tpe == IntClass.tpe => Some(c.intValue)
      case _ => None
    }
  }

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

  object ExIntIdentifier {
    def unapply(tree: Tree): Option[Ident] = tree match {
      case i: Ident if i.tpe == IntClass.tpe => Some(i)
      case _ => None
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

  
  object ExEquals {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, n), List(rhs)) if (lhs.tpe == IntClass.tpe && rhs.tpe == IntClass.tpe) => // && n == nme.EQ) =>
        Some((lhs,rhs))
      case _ => None
    }
  }
}
