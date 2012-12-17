package synthesis.ordered

import synthesis.ordered.AST.{Formula, Ident}
import synthesis.ordered.Primitives.IntType

/**
 * A class for symbols, i.e. globally-unique names.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

class Symbol private(val name: String) {
  override def toString: String = name
}

object Symbol {
  private val counters = scala.collection.mutable.HashMap[String, Int]()
  private val interned = scala.collection.mutable.HashMap[String, Symbol]()

  private def freshName(prefix: String): String = {
    val count = counters.getOrElse(prefix, 1)
    counters.put(prefix, count + 1)
    prefix + "." + count
  }

  private def lookup(name: String): Symbol = interned get name match {
    case Some(sym) => sym
    case None =>
      val sym = new Symbol(name)
      interned.put(name, sym)
      sym
  }

  def apply(name: String) = {
    if (name contains '.') error("bad identifier: " + name)
    lookup(name)
  }

  //  def fresh(prefix: String): Symbol =
  //    new Symbol(freshName(prefix))

  def freshInt: Symbol =
    new Symbol(freshName("t"))

  def freshSet: Symbol =
    new Symbol(freshName("S"))

  def equiClass(k: Int): Symbol =
    lookup("[" + k + "]")

  def equiRange(k: Int): Symbol =
    lookup("[" + k + ":" + (k + 1) + "]")

  def partClass(setvar: Ident, k: Int): Symbol =
    lookup(setvar.name + "." + k)

  def partRange(setvar: Ident, k: Int): Symbol =
    lookup(setvar.name + "." + k + ":" + (k + 1))

  def infOf(setvar: Ident): Symbol =
    lookup("inf." + setvar.name)

  def supOf(setvar: Ident): Symbol =
    lookup("sup." + setvar.name)

  def beta(k: Int, setvar: Ident): Symbol =
    lookup("pp." + k + "_" + setvar.name)

  def vennSize(k: Int): Symbol =
    lookup("ll." + k)

  def ifThenElse(k: Int): Symbol =
    lookup("if." + k)
}
