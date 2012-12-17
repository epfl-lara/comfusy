package object synthesis {
  implicit class ListOps[A](val xs: List[A]) extends AnyVal {
    def remove(p: A => Boolean) = xs filterNot p
    def -(x: A) = xs filterNot (_ == x)
    def --(ys: Traversable[A]) = xs filterNot ys.toSet
  }
}
