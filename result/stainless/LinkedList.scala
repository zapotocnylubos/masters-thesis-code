import stainless.lang._
import stainless.collection._
import stainless.annotation._

sealed abstract class LinkedList {
  def content: Set[Int] = this match {
    case Nil() => Set.empty
    case Cons(h, t) => Set(h) ++ t.content
  }

  def contains(x: Int): Boolean = {
    this match {
      case Nil() => false
      case Cons(h, t) => h == x || t.contains(x)
    }
  }.ensuring(res => res == content.contains(x))

  def prepend(x: Int): LinkedList = {
    Cons(x, this)
  }.ensuring(res => res.content == Set(x) ++ content)

  def append(x: Int): LinkedList = {
    this match {
      case Nil() => Cons(x, Nil())
      case Cons(h, t) => Cons(h, t.append(x))
    }
  }.ensuring(res => res.content == content ++ Set(x))

  def remove(x: Int): LinkedList = {
    this match {
      case Nil() => Nil()
      case Cons(h, t) => if (h == x) t.remove(x) else Cons(h, t.remove(x))
    }
  }.ensuring(res =>
    contains(x) ==> (res.content == content -- Set(x))
    && !contains(x) ==> (res.content == content)
  )
}

case class Nil() extends LinkedList
case class Cons(head: Int, tail: LinkedList) extends LinkedList
