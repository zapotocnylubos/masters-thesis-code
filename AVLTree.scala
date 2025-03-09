import stainless.lang._
import stainless.collection._
import stainless.annotation._

sealed abstract class AVLTree {
  def content: Set[Int] = this match {
    case Leaf() => Set.empty
    case Node(v, l, r, _) => l.content ++ Set(v) ++ r.content
  }

  def height: Int = this match {
    case Leaf() => 0
    case Node(_, _, _, h) => h
  }

  def balanceFactor: Int = {
    this match {
      case Leaf() => 0
      case Node(_, l, r, _) => l.height - r.height
    }
  }

  def hasBinarySearchTreeStructure: Boolean = this match {
    case Leaf() => true
    case Node(v, l, r, _) => {
      l.hasBinarySearchTreeStructure &&
        r.hasBinarySearchTreeStructure &&
        // Ensure that the AVL has a binary search tree structure
        forall((x: Int) => l.content.contains(x) ==> x < v) &&
        forall((x: Int) => r.content.contains(x) ==> x > v)
    }
  }

  def hasAVLTreeStructure: Boolean = this match {
    case Leaf() => true
    case Node(v, l, r, _) => {
      l.hasAVLTreeStructure &&
        r.hasAVLTreeStructure &&
        // Ensure that the height of the tree at most (at root) is Int.MaxValue
        l.height < Int.MaxValue &&
        r.height < Int.MaxValue &&
        // Ensure that the height of the tree is correct
        height == 1 + (l.height < r.height match {
          case true => r.height
          case false => l.height
        })
    }
  }

  def isBalanced: Boolean = this match {
    case Leaf() => true
    case Node(v, l, r, _) => {
      l.isBalanced &&
        r.isBalanced &&
        // Ensure that the balance factor is within [-1, 1]
        balanceFactor >= -1 &&
        balanceFactor <= 1
    }
  }

  def isAVLTree: Boolean = this match {
    case Leaf() => true
    case Node(v, l, r, h) => {
      l.isAVLTree &&
        r.isAVLTree &&
        hasBinarySearchTreeStructure &&
        hasAVLTreeStructure &&
        isBalanced
    }
  }

  def contains(x: Int): Boolean = {
    require(isAVLTree)
    this match {
      case Leaf() => false
      case Node(v, l, r, _) => {
        if (x == v) true
        else if (x < v) l.contains(x)
        else r.contains(x)
      }
    }
  }.ensuring(res => res == content.contains(x))
}

case class Leaf() extends AVLTree

case class Node
(
  value: Int,
  left: AVLTree,
  right: AVLTree,
  _height: Int
) extends AVLTree {
  require(_height > 0)

  def min: Int = {
    require(isAVLTree)
    this match {
      case Node(v, Leaf(), _, _) => v
      case Node(_, l: Node, _, _) => l.min
    }
  }.ensuring(res =>
    content.contains(res) &&
      forall((x: Int) => (content.contains(x) && x != res) ==> x > res)
  )

  def max: Int = {
    require(isAVLTree)
    this match {
      case Node(v, _, Leaf(), _) => v
      case Node(_, _, r: Node, _) => r.max
    }
  }.ensuring(res =>
    contains(res) &&
      forall((x: Int) => (contains(x) && x != res) ==> x < res)
  )

  def rotateLeft: Node = {
    require(hasBinarySearchTreeStructure)
    require(hasAVLTreeStructure)
    require(balanceFactor == 2 && right.balanceFactor == 1)
    require(left.isAVLTree)
    require(right.isAVLTree)
    require(right.isInstanceOf[Node])

    right match {
      case Node(v, rl, rr, _) =>
        Node(
          v,
          Node(value, left, rl, 1 + left.height),
          rr,
          1 + (value < rr.height match {
            case true => rr.height
            case false => value
          })
        )
    }
  }.ensuring(res => res.content == content &&
    res.right.isAVLTree &&
    res.left.isInstanceOf[Node] ==> (res.left.asInstanceOf[Node].value == old(this).value)
  )
   //&& res.isAVLTree)
}
