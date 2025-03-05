import stainless.lang._
import stainless.collection._
import stainless.annotation._

sealed abstract class BinarySearchTree {
  def content: Set[Int] = this match {
    case Leaf() => Set.empty
    case Node(v, l, r) => l.content ++ Set(v) ++ r.content
  }

  def isBinarySearchTree: Boolean = this match {
    case Leaf() => true
    case Node(v, l, r) => {
      l.isBinarySearchTree &&
        r.isBinarySearchTree &&
        forall((x: Int) => l.content.contains(x) ==> x < v) &&
        forall((x: Int) => r.content.contains(x) ==> x > v)
    }
  }

  def contains(x: Int): Boolean = {
    require(isBinarySearchTree)
    this match {
      case Leaf() => false
      case Node(v, l, r) => {
        if (x == v) true
        else if (x < v) l.contains(x)
        else r.contains(x)
      }
    }
  }.ensuring(res => res == content.contains(x))

  def insert(x: Int): BinarySearchTree = {
    require(isBinarySearchTree)
    this match {
      case Leaf() => Node(x, Leaf(), Leaf())
      case Node(v, l, r) => {
        if (x == v) this
        else if (x < v) Node(v, l.insert(x), r)
        else Node(v, l, r.insert(x))
      }
    }
  }.ensuring(res => res.isBinarySearchTree && res.content == content ++ Set(x))

  def delete(x: Int): BinarySearchTree = {
    require(isBinarySearchTree)
    this match {
      case Leaf() => this
      case Node(v, l, r) => {
        if (x == v) {
          (l, r) match {
            case (Leaf(), Leaf()) => Leaf()
            case (Leaf(), Node(_, _, _)) => r
            case (Node(_, _, _), Leaf()) => l
            case (Node(_, _, _), r2: Node) => {
              val m = r2.min
              Node(m, l, r2.delete(m))
            }
          }
        } else if (x < v) Node(v, l.delete(x), r)
        else Node(v, l, r.delete(x))

      }
    }
  }.ensuring(res => res.content == this.content -- Set(x)) // res.isBinarySearchTree &&
}

case class Leaf() extends BinarySearchTree

case class Node
(
  value: Int,
  left: BinarySearchTree,
  right: BinarySearchTree,
) extends BinarySearchTree {
  def min: Int = {
    require(isBinarySearchTree)
    this match {
      case Node(v, Leaf(), _) => v
      case Node(_, l: Node, _) => l.min
    }
  }.ensuring(res => contains(res) && forall((x: Int) => contains(x) ==> res <= x))

  def max: Int = {
    require(isBinarySearchTree)
    this match {
      case Node(v, _, Leaf()) => v
      case Node(_, _, r: Node) => r.max
    }
  }.ensuring(res => contains(res) && forall((x: Int) => contains(x) ==> x <= res))
}
