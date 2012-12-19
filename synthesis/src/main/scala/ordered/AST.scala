package synthesis.ordered

import scala.text.Document
import Document._
import Primitives._

object AST {
  type Name = Symbol
  //  type Logical = Primitives.Logical
  //  type NonLogical = Primitives.NonLogical


  implicit def sym2term(s: Symbol): Ident = Ident(if (s.name(0).isUpper) SetType else IntType, s)

  implicit def int2term(i: Int): Term = Lit(IntLit(i))

  val emptyset = AST.Lit(EmptySetLit)


  sealed abstract class Formula {
    def print {Printer print (Printer toDocument this)}

    def &&(form: Formula, forms: Formula*) = And(this :: form :: forms.toList)
    //    def ||(form: Formula, forms: Formula*) = Or(this :: form :: forms.toList)
    def ||(forms: Formula*) = if (forms isEmpty) this else Or(this :: forms.toList)

    def unary_! = Not(this)
  }
  case object True extends Formula
  case object False extends Formula
  case class Not(formula: Formula) extends Formula
  case class And(formulas: List[Formula]) extends Formula
  case class Or(formulas: List[Formula]) extends Formula
  case class Predicate(comp: Logical, terms: List[Term]) extends Formula

  sealed abstract class Term {
    def print {Printer print (Printer toDocument this)}

    def <(term: Term) = Predicate(LT, List(this, term))

    def <=(term: Term) = Predicate(LE, List(this, term))

    def ===(term: Term) = Predicate(EQ, List(this, term))

    def =!=(term: Term) = Predicate(NE, List(this, term))

    def >(term: Term) = Predicate(GT, List(this, term))

    def >=(term: Term) = Predicate(GE, List(this, term))

    def seq(term: Term) = Predicate(SEQ, List(this, term))

    def slt(term: Term) = Predicate(SLT, List(this, term))

    def selem(term: Term) = Predicate(SELEM, List(this, term))

    def subseteq(term: Term) = Predicate(SUBSETEQ, List(this, term))

    def +(term: Term, terms: Term*) = Op(ADD, this :: term :: terms.toList)

    def -(term: Term) = Op(SUB, List(this, term))

    def *(term: Term, terms: Term*) = Op(MUL, this :: term :: terms.toList)

    def ++(term: Term) = Op(UNION, List(this, term))

    def **(term: Term) = Op(INTER, List(this, term))

    def --(term: Term) = Op(MINUS, List(this, term))

    def lrange(from: Term, to: Term) = Op(LRANGE, List(from, to, this))

    def take(term: Term) = Op(TAKE, List(term, this))

    def card = Op(CARD, List(this))

    def sup = Op(SUP, List(this))

    def inf = Op(INF, List(this))

    def unary_~ = Op(COMPL, List(this))
    //    def compl = Op(COMPL, List(this))
  }
  case class Ident(tpe: Type, name: Name) extends Term
  case class Lit(value: Literal) extends Term
  case class Op(op: NonLogical, terms: List[Term]) extends Term


  /**Pretty printer **/

  private object Printer {
    private implicit def stringToDoc(s: String): Document = text(s)

    private implicit def intToDoc(i: Int): Document = text(i.toString)

    // Helper methods
    def paren(d: Document): Document =
      group("(" :: nest(2, d) :: ")")

    def toDocument(f: Formula): Document = f match {
      case True => "true"
      case False => "false"
      case Not(f@Predicate(_, _)) => "\u00AC" :/: paren(toDocument(f))
      case Not(f) => "\u00AC" :/: toDocument(f)
      case And(fs) =>
        //        paren( repsep(fs map toDocument, "\u2227") )
        paren(repsep(fs map toDocument, "n"))
      case Or(fs) =>
        //        paren( repsep(fs map toDocument, "\u2228") )
        paren(repsep(fs map toDocument, "v"))
      case Predicate(op, t :: Nil) =>
        op.toString :/: paren(toDocument(t))
      case Predicate(op, ts) =>
        paren(repsep(ts map toDocument, op toString))
    }

    def toDocument(f: Term): Document = f match {
      case Ident(_, name) => name toString
      case Lit(EmptySetLit) => "{}"
      case Lit(UniversalSetLit) => "{ALL}"
      case Lit(IntLit(value)) => value
      case Op(op, t :: Nil) =>
        op.toString :/: toDocument(t)
      case Op(op@(LRANGE | TAKE), ts) =>
        op.toString :/: paren(repsep(ts map toDocument, ","))
      case Op(ITE(f), List(t, s)) =>
        group("if" :/: toDocument(f) :/: "then" :/: toDocument(t) :/: "else" :/: toDocument(s))
      case Op(op, ts) =>
        paren(repsep(ts map toDocument, op toString))
    }

    def repsep(doc: List[Document], sep: Document): Document =
      if (doc isEmpty) empty else
        doc.reduceLeft {(rest, d) => rest :/: group(sep :/: d)}

    def print(doc: Document) {
      val writer = new java.io.PrintWriter(System.out)
      doc.format(200, writer)
      writer.println()
      writer.flush()
    }
  }

}
/*
object AST1 extends AST {
  import Primitives.{IntLogical, negate}

  type Name = Symbol
  type Logical = Primitives.Logical
  type NonLogical = Primitives.NonLogical


}*/
