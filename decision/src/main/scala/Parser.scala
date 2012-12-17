package decision

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._
import AST._
import Primitives._

object FormulaParser extends StandardTokenParsers {
  lexical.delimiters ++= List("<=>", "(", ")", "=", "=>", "&&", "||", "!", "+", "-", "*", "<", "<=", ">", ">=", "!=", "**", "++", "--", "ALL", "{}", "~", ",", "<<", "==", "|", ".", "{", "}")
  lexical.reserved ++= List("true", "false", "selem", "subseteq", "seq", "card", "slt", "inf", "sup", "subset", "ALL", "lrange", "in", "compl")

  def SubExpr: Parser[Term] = positioned(
    "{}" ^^^ emptyset
            | "ALL" ^^^ fullset
            | "{" ~> SimpleTerm <~ "}" ^^ {case x => x.singleton}
            | ident ^^ {case x => TermVar(Symbol(x))}
            | numericLit ^^ {case x => Lit(IntLit(x.toInt))}
            | "inf" ~> "(" ~> SimpleTerm <~ ")" ^^ {case t1 => t1.inf}
            | "sup" ~> "(" ~> SimpleTerm <~ ")" ^^ {case t1 => t1.sup}
            | "card" ~> "(" ~> SimpleTerm <~ ")" ^^ {case t1 => t1.card}
            | "compl" ~> "(" ~> SimpleTerm <~ ")" ^^ {case t1 => ~t1}
            | "|" ~> SimpleTerm <~ "|" ^^ {case t1 => t1.card}
            | "take" ~> "(" ~> SimpleTerm ~ ("," ~> SimpleTerm) <~ ")" ^^ {case t1 ~ t2 => t1.take(t2)}
            | "lrange" ~> "(" ~> SimpleTerm ~ ("," ~> SimpleTerm) ~ ("," ~> SimpleTerm) <~ ")" ^^ {case t1 ~ t2 ~ t3 => t1.lrange(t2, t3)}
            | failure("Ill formed subterm")
    )

  def SimpleTerm: Parser[Term] = positioned(
    "(" ~> SimpleTerm <~ ")"
            | "~" ~> SimpleTerm ^^ {case x => ~x}
            | (SubExpr <~ "+") ~ SimpleTerm ^^ {case t1 ~ t2 => t1 + t2}
            | (SubExpr <~ "-") ~ SimpleTerm ^^ {case t1 ~ t2 => t1 - t2}
            | (SubExpr <~ "*") ~ SimpleTerm ^^ {case t1 ~ t2 => t1 * t2}
            | (SubExpr <~ "**") ~ SimpleTerm ^^ {case t1 ~ t2 => t1 ** t2}
            | (SubExpr <~ "++") ~ SimpleTerm ^^ {case t1 ~ t2 => t1 ++ t2}
            | (SubExpr <~ "--") ~ SimpleTerm ^^ {case t1 ~ t2 => t1 -- t2}
            | SubExpr
            | failure("Ill formed term")
    )

  def Atom: Parser[Formula] = positioned(
    "true" ^^^ True
            | "false" ^^^ False
            | "(" ~> CompleteFormula <~ ")"
            | "!" ~> Atom ^^ {case x => !x}
            | (SimpleTerm <~ "selem") ~ SimpleTerm ^^ {case x ~ y => x selem y}
            | (SimpleTerm <~ "in") ~ SimpleTerm ^^ {case x ~ y => x selem y}
            | (SimpleTerm <~ "subseteq") ~ SimpleTerm ^^ {case x ~ y => x subseteq y}
            | (SimpleTerm <~ "subset") ~ SimpleTerm ^^ {case x ~ y => (x subseteq y) && !(x seq y)}
            | (SimpleTerm <~ "slt") ~ SimpleTerm ^^ {case x ~ y => x slt y}
            | (SimpleTerm <~ "<<") ~ SimpleTerm ^^ {case x ~ y => x slt y}
            | (SimpleTerm <~ "seq") ~ SimpleTerm ^^ {case x ~ y => x seq y}
            | (SimpleTerm <~ "=") ~ SimpleTerm ^^ {case x ~ y => x === y}
            | (SimpleTerm <~ "==") ~ SimpleTerm ^^ {case x ~ y => x seq y}
            | (SimpleTerm <~ "!=") ~ SimpleTerm ^^ {case x ~ y => x =!= y}
            | (SimpleTerm <~ "<") ~ SimpleTerm ^^ {case x ~ y => x < y}
            | (SimpleTerm <~ "<=") ~ SimpleTerm ^^ {case x ~ y => x <= y}
            | (SimpleTerm <~ ">=") ~ SimpleTerm ^^ {case x ~ y => x >= y}
            | (SimpleTerm <~ ">") ~ SimpleTerm ^^ {case x ~ y => x > y}
            | failure("Illegal formula")
    )

  def CompleteFormula: Parser[Formula] = positioned(
    (Atom <~ "&&") ~ CompleteFormula ^^ {case f ~ l => And(f :: l :: Nil)}
            | (Atom <~ "||") ~ CompleteFormula ^^ {case f ~ l => Or(f :: l :: Nil)}
            | (Atom <~ "=>") ~ Atom ^^ {case a ~ c => a implies c}
            | (Atom <~ "<=>") ~ Atom ^^ {case f1 ~ f2 => (f1 && f2) || (!f1 && !f2)}
            | Atom
            | failure("Illegal Formula")
    )

  def getFromStream(stream: StreamReader): Formula = {
    val tokens = new lexical.Scanner(stream)
    println("Starting parsing.")
    phrase(FormulaParser.CompleteFormula)(tokens) match {
      case Success(form, _) => form
      case e => throw (new Exception("Exception = " + e))
    }
  }

  def main(args: Array[String]) = {
    getFromStream(StreamReader(new java.io.InputStreamReader(System.in)))
  }
}

object Parser {
  // Dummy
}
