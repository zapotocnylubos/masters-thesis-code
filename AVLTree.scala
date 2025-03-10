import stainless.lang._
import stainless.collection._
import stainless.annotation._

def int_max(x: Int, y: Int): Int = if (x > y) x else y

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
      case Node(_, l, r, _) => r.height - l.height
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

  def insert(x: Int): AVLTree = {
    require(isAVLTree)
    require(height < Int.MaxValue)

    this match {
      case Leaf() => Node(x, Leaf(), Leaf(), 1)
      case Node(v, l, r, _) => {
        if (x == v) this
        else if (x < v) {
          val newLeft = l.insert(x)
          assert(newLeft.isAVLTree)
          Node(v, newLeft, r, 1 + int_max(newLeft.height, r.height)).balance
        } else {
          val newRight = r.insert(x)
          assert(newRight.isAVLTree)
          Node(v, l, newRight, 1 + int_max(l.height, newRight.height)).balance
        }
      }
    }
  }.ensuring(res => res.isAVLTree && res.content == content ++ Set(x))
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
    require(left.isAVLTree && right.isAVLTree)
    require(balanceFactor == 2 && right.balanceFactor >= 0)

    right match {
      case Node(v, rl, rr, _) =>
        Node(
          v,
          Node(value, left, rl, 1 + int_max(left.height, rl.height)),
          rr,
          1 + int_max(
            1 + int_max(left.height, rl.height),
            rr.height
          )
        )
    }
  }.ensuring(res => res.content == content && res.isAVLTree)

  def rotateRight: Node = {
    require(hasBinarySearchTreeStructure)
    require(hasAVLTreeStructure)
    require(left.isAVLTree && right.isAVLTree)
    require(balanceFactor == -2 && left.balanceFactor <= 0)

    left match {
      case Node(v, ll, lr, _) =>
        Node(
          v,
          ll,
          Node(value, lr, right, 1 + int_max(lr.height, right.height)),
          1 + int_max(
            1 + int_max(lr.height, right.height),
            ll.height
          )
        )
    }
  }.ensuring(res => res.content == content && res.isAVLTree)

  def rotateLeftRight: Node = {
    require(hasBinarySearchTreeStructure)
    require(hasAVLTreeStructure)
    require(left.isAVLTree && right.isAVLTree)
    require(balanceFactor == -2 && left.balanceFactor == 1)

    left match {
      case Node(v, ll, lr, _) =>
        lr match {
          case Node(vlr, lrl, lrr, _) =>
            Node(
              vlr,
              Node(v, ll, lrl, 1 + int_max(ll.height, lrl.height)),
              Node(value, lrr, right, 1 + int_max(lrr.height, right.height)),
              1 + int_max(
                1 + int_max(ll.height, lrl.height),
                1 + int_max(lrr.height, right.height)
              )
            )
        }
    }
  }.ensuring(res => res.content == content && res.isAVLTree)

  def rotateRightLeft: Node = {
    require(hasBinarySearchTreeStructure)
    require(hasAVLTreeStructure)
    require(left.isAVLTree && right.isAVLTree)
    require(balanceFactor == 2 && right.balanceFactor == -1)

    right match {
      case Node(v, rl, rr, _) =>
        rl match {
          case Node(vrl, rll, rlr, _) =>
            Node(
              vrl,
              Node(value, left, rll, 1 + int_max(left.height, rll.height)),
              Node(v, rlr, rr, 1 + int_max(rlr.height, rr.height)),
              1 + int_max(
                1 + int_max(left.height, rll.height),
                1 + int_max(rlr.height, rr.height)
              )
            )
        }
    }
  }.ensuring(res => res.content == content && res.isAVLTree)

  def balance: Node = {
    require(hasBinarySearchTreeStructure)
    require(hasAVLTreeStructure)
    require(left.isAVLTree && right.isAVLTree)
    require(-2 <= balanceFactor && balanceFactor <= 2)

    if (balanceFactor == 2) {
      if (right.balanceFactor == -1) rotateRightLeft
      else rotateLeft
    } else if (balanceFactor == -2) {
      if (left.balanceFactor == 1) rotateLeftRight
      else rotateRight
    } else this
  }.ensuring(res => res.isAVLTree && res.content == content)
}
