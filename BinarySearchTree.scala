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
        l.content.forall(_ < v) &&
        r.content.forall(_ > v)
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

  // Node(268436689,
  //   Node(205521960,
  //     Leaf(),
  //     Node(341835778, Leaf(), Leaf())
  //   ),
  //   Node(268436728,
  //     Node(201327776, Leaf(), Leaf()),
  //     Node(270599420, Leaf(), Leaf())
  //   )
  // )

//  def insert(x: Int): BinarySearchTree = ({
//    require(isBinarySearchTree)
//    this match {
//      case Leaf() => Node(x, Leaf(), Leaf())
//      case Node(v, l, r) => {
//        if (x == v) this
//        else if (x < v) Node(v, l.insert(x), r)
//        else Node(v, l, r.insert(x))
//      }
//    }
//  }).ensuring(res => res.isBinarySearchTree && res.content == this.content ++ Set(x))

  //  def delete(x: Int): BinarySearchTree = ({
  //    require(isBinarySearchTree)
  //    this match {
  //      case Leaf() => this
  //      case Node(v, l, r) => {
  //        if (x == v) {
  //          (l, r) match {
  //            case (Leaf(), Leaf()) => Leaf()
  //            case (Leaf(), Node(vr, _, _)) => Node(vr, Leaf(), Leaf())
  //            case (Node(vl, _, _), Leaf()) => Node(vl, Leaf(), Leaf())
  //            case (Node(vl, _, _), Node(vr, _, _)) => {
  //              val min = r.min
  //              Node(min, l, r.delete(min))
  //            }
  //          }
  //        } else if (x < v) Node(v, l.delete(x), r)
  //        else Node(v, l, r.delete(x))
  //
  //      }
  //    }
  //  }).ensuring(res => res.isBinarySearchTree && res.content == this.content -- Set(x))
}

case class Leaf() extends BinarySearchTree

case class Node
(
  value: Int,
  left: BinarySearchTree,
  right: BinarySearchTree,
) extends BinarySearchTree {
  //  def min: Int = {
  //    require(isBinarySearchTree)
  //    this match {
  //      case Node(v, Leaf(), _) => v
  //      case Node(_, l: Node, _) => l.min
  //    }
  //  }.ensuring (res => contains(res)) // && content.forall(res <= _)
}
