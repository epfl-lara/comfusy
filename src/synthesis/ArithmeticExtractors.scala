package synthesis

/** Helper extractors to pull out these pesky arithmetic expressions. */
trait ArithmeticExtractors {
  self: ChooseTransformer =>
  import global._
  import global.definitions._

  //import scala.collection.mutable.Set

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

  // extractors for set expressions
  object ExSubsetOf {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n.toString == "subsetOf") => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExSetCard {
    def unapply(tree: Tree): Option[Tree] = tree match {
      case Select(t, n) if (n.toString == "size") => Some(t)
      case _ => None
    }
  }

  object ExUnion {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == nme.PLUSPLUS) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExIntersection {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == encode("**")) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExSetMinus {
    def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if (n == encode("--")) => Some((lhs,rhs))
      case _ => None
    }
  }

  private lazy val setTraitSym = definitions.getClass("scala.collection.immutable.Set")

  object ExSetIdentifier {
    def unapply(tree: Tree): Option[Ident] = tree match {
      case i: Ident => i.symbol.tpe match {
          case TypeRef(_,sym,_) if sym == setTraitSym => Some(i)
          case _ => None
        }
      case _ => None
    }
  }

  object ExEmptySet {
    def unapply(tree: Tree): Boolean = tree match {
      case TypeApply(
        Select(
          Select(
            Select(
              Select(Ident(s), collectionName),
              immutableName),
            setName),
          emptyName),  _ :: Nil) => {
          collectionName.toString == "collection" && immutableName.toString == "immutable" && setName.toString == "Set" && emptyName.toString == "empty"
        }
      case _ => false
    }
  }

  private lazy val synthModule    = definitions.getModule("synthesis") 
  private lazy val synthDefModule = definitions.getModule("synthesis.Definitions")

  object ExExGeneric {
    def ua(tree: Tree, opName: Name) : Option[(Tree,Tree)] = tree match {
      case UnApply(
        Apply(
          Select(
            Select(
              Select(i: Ident, n1),
              n2),
            n3),
          List(Ident(nme.SELECTOR_DUMMY)))
        , t1 :: t2 :: Nil) if (
           i.symbol == synthModule
        && n1 == synthDefModule.name
        && n2 == opName
        && n3.toString == "unapply") => Some((t1,t2))
      case _ => None
    }
  }

  // Extractors that extract calls to extractors...
  object ExExTimes {
    def unapply(tree: Tree) : Option[(Tree,Tree)] = ExExGeneric.ua(tree, nme.MUL)
  }

  object ExExPlus {
    def unapply(tree: Tree) : Option[(Tree,Tree)] = ExExGeneric.ua(tree, nme.ADD)
  }

  object ExExMinus {
    def unapply(tree: Tree) : Option[(Tree,Tree)] = ExExGeneric.ua(tree, nme.SUB)
  }
}
