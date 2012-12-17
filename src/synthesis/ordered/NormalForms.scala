package synthesis.ordered

object NormalForms {
  import synthesis.ordered.AST._
  import synthesis.ordered.Primitives._

  // chains all transformations
  def apply(formula: Formula) = dnf(nnf(formula)) map rewrite map And

  /**Normal form transformations **/

  // TODO: Any reason they are private
  // RS: Not really. I only use them as shortcutrs for their types.
  private type Conjunction = List[Formula]
  private type DNF = Stream[Conjunction]

  // Complete dnf transformation
  def dnf(f: Formula): DNF = f match {
    case And(Nil) => Stream(Nil)
    case And(c :: Nil) => dnf(c)
    case And(c :: cs) =>
      for (conj1 <- dnf(c); conj2 <- dnf(And(cs)))
      yield conj1 ++ conj2
    case Or(Nil) => Stream(List(False))
    case Or(d :: Nil) => dnf(d)
    case Or(d :: ds) => dnf(d) append dnf(Or(ds))
    case Not(And(_) | Or(_)) =>
      // dnf(nnf(f))
      error("Not in negated normal form !")
    case _ => Stream(f :: Nil)
  }


  // Partial dnf transformation
  // The relevant atoms for the ordered decision procedure are in dnf form
  def pdnf(f: Formula): DNF = if (!isAtom(f)) Stream(f :: Nil) else f match {
    case And(Nil) => Stream(Nil)
    case And(c :: Nil) => pdnf(c)
    case And(c :: cs) =>
      for (conj1 <- pdnf(c); conj2 <- pdnf(And(cs)))
      yield conj1 ++ conj2
    case Or(Nil) => Stream(List(False))
    case Or(d :: Nil) => pdnf(d)
    case Or(d :: ds) => pdnf(d) append pdnf(Or(ds))
    case Not(And(_) | Or(_)) =>
      // pdnf(nnf(f))
      error("Not in negated normal form !")
    case _ => Stream(f :: Nil)
  }

  private def isAtom(f: Formula): Boolean = f match {
    case True | False => false
    case Not(f) => isAtom(f)
    case And(fs) => fs exists isAtom
    case Or(fs) => fs exists isAtom
    case Predicate(SELEM | SLT, _) => true
    case Predicate(_, fs) => fs exists isAtom
  }

  private def isAtom(t: Term): Boolean = t match {
    case Op(LRANGE | TAKE | INF | SUP, _) => true
    case _ => false
  }


  // Negated normal form with and/or flattening
  def nnf(f: Formula): Formula = f match {
    case True | False | Predicate(_, _) => f
    case And(fs) =>
      val formulas = fs map nnf remove {_ == True}
      if (formulas contains False) False
      else formulas flatMap flatAnd match {
        case Nil => True
        case f :: Nil => f
        case fs => And(fs)
      }
    case Or(fs) =>
      val formulas = fs map nnf remove {_ == False}
      if (formulas contains True) True
      else formulas flatMap flatOr match {
        case Nil => False
        case f :: Nil => f
        case fs => Or(fs)
      }
    case Not(Not(p)) => nnf(p)
    case Not(And(fs)) => nnf(Or(fs map Not))
    case Not(Or(fs)) => nnf(And(fs map Not))
    case Not(True) => False
    case Not(False) => True
    case Not(Predicate(op: IntLogical, terms)) =>
      Predicate(negate(op), terms)
    case Not(_) => f
  }

  private def flatAnd(f: Formula) = f match {
    case And(fs) => fs
    case _ => List(f)
  }

  private def flatOr(f: Formula) = f match {
    case Or(fs) => fs
    case _ => List(f)
  }


  /**Rewrite compound primitives and make INF/SUP operations pure **/

  def rewrite(formulas: Conjunction): Conjunction = formulas flatMap rewrite

  // TODO Should this not return the definitions of newly introduced termVariables
  // Or would it be a state variable in the class?
  // RS: I'd rather keep the definitions in the formula so we don't need to
  //     merge them back. If it turns out to be difficult to get the definition
  //     of a variable we could use a new primitive to tag definitions.
  //     (i.e. create 'case class DEF extends Primitive(":=")' and replace EQ by DEF)
  def rewrite(f: Formula): Conjunction = f match {
    case Predicate(SELEM, List(t, _s)) =>
      rewritePure(t, tf => rewriteNonPure(_s, s => {
        val af = Symbol.freshSet
        // TODO would it help to add s.card > 0 ?
        // UU: No, Bapa adds these constraints
        // RS: Our decision procedure should not guess s to be empty ...
        //     (This applies only if s is a variable)
        (af.card === 1) :: (af.inf === tf) :: (af.sup === tf) ::
                (af subseteq s) :: Nil
      }))
    case Not(Predicate(SELEM, List(t, s))) =>
      rewrite(Predicate(SELEM, List(t, ~s)))

    case Predicate(SLT, args) =>
      rewritePure_*(args, xs => (xs: @unchecked) match {
        case s1 :: s2 :: Nil =>
          val supf = Symbol.supOf(s1)
          val inff = Symbol.infOf(s2)
          (supf < inff) :: (supf === s1.sup) :: (inff === s2.inf) :: Nil
      })
    case Not(Predicate(SLT, args)) =>
      rewritePure_*(args, xs => (xs: @unchecked) match {
        case s1 :: s2 :: Nil =>
          val supf = Symbol.supOf(s1)
          val inff = Symbol.infOf(s2)
          (supf >= inff) :: (supf === s1.sup) :: (inff === s2.inf) :: Nil
      })
    case Predicate(EQ, List(t, Op(op@(SUP | INF), List(s)))) =>
      rewritePure(t, tf =>
        rewritePure(s, sf =>
          (tf === Op(op, List(sf))) :: Nil
          ))
    case Predicate(EQ, List(Op(op@(SUP | INF), List(s)), t)) =>
      rewritePure(s, sf =>
        rewritePure(t, tf =>
          (tf === Op(op, List(sf))) :: Nil
          ))
    case Predicate(comp, terms) =>
      rewriteNonPure_*(terms, ts => Predicate(comp, ts) :: Nil)

    case True | False =>
      error("A simplified conjunction cannot contain " + f)

    case And(_) | Or(_) if isAtom(f) =>
      error("A simplified conjunction cannot contain " + f)

    case _ => List(f)
  }

  private def rewritePure(term: Term, ctx: Ident => Conjunction) = term match {
    case id@Ident(_, _) => ctx(id)
    case _ =>
      val tf = Symbol.freshInt
      rewriteNonPure(term, t => (tf === t) :: ctx(tf))
  }

  private def rewriteNonPure(term: Term, ctx: Term => Conjunction): Conjunction = term match {
    case Op(op@(INF | SUP), List(s)) =>
      rewritePure(s, sf => {
        val tf = Symbol.freshInt
        (tf === Op(op, List(sf))) :: ctx(tf)
      })

    case Op(TAKE, List(t, s)) =>
      val af = Symbol.freshSet
      (t === af.card) :: rewrite(af slt (s -- af)) ::: ctx(af)

    case Op(LRANGE, List(t1, t2, s)) =>
      rewritePure(s, sf => {
        val term = (sf take t2) -- (sf take (t1 - 1))
        rewriteNonPure(term, ctx)
      })

    case Op(op, terms) =>
      rewriteNonPure_*(terms, ts => ctx(Op(op, ts)))

    case _ => ctx(term)
  }

  private def rewritePure_*(trees: List[Term], ctx: List[Ident] => Conjunction): Conjunction =
    trees match {
      case Nil => ctx(Nil)
      case t :: ts =>
        rewritePure(t, tSym => rewritePure_*(ts, tSyms => ctx(tSym :: tSyms)))
    }

  private def rewriteNonPure_*(trees: List[Term], ctx: List[Term] => Conjunction): Conjunction =
    trees match {
      case Nil => ctx(Nil)
      case t :: ts =>
        rewriteNonPure(t, tSym => rewriteNonPure_*(ts, tSyms => ctx(tSym :: tSyms)))
    }

}
