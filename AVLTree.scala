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


    //    node* leftRotation(node* current) {
    //        node* new_node = current->right;
    //        current->right = new_node->left;
    //        new_node->left = current;
    //        current->height = 1 + max(height(current->left), height(current->right));
    //        new_node->height = 1 + max(height(new_node->left), height(new_node->right));
    //        return new_node;
    //    }

    right match {
      case Node(rv, rl, rr, _) =>
        Node(
          rv,
          Node(value, left, rl, 1 + int_max(left.height, rl.height)),
          rr,
          1 + int_max(
            1 + int_max(left.height, rl.height),
            rr.height
          )
        )
    }
  }.ensuring(res => res.content == content &&
    res.right.isAVLTree &&
    res.left.isInstanceOf[Node] ==> (res.left.asInstanceOf[Node].value == old(this).value) &&
    res.left.isInstanceOf[Node] ==> (res.left.asInstanceOf[Node].left == old(this).left) &&
    res.left.isInstanceOf[Node] ==> (res.left.asInstanceOf[Node].right == old(this).right.asInstanceOf[Node].left) &&
    res.left.hasBinarySearchTreeStructure &&
    res.left.hasAVLTreeStructure &&
    res.right.hasBinarySearchTreeStructure &&
    res.right.hasAVLTreeStructure &&
    res.right.isBalanced &&
    res.left.balanceFactor >= -1 &&
    res.left.balanceFactor <= 3
    && res.balanceFactor <= 5 // knowledge probing -> <= 30, 15, 10, 6, 5 -> OK, <= 4 -> NOK
    // Knowledge probing about left rotation subtrees
    && ((res.left.isInstanceOf[Node] && res.left.asInstanceOf[Node].left.isInstanceOf[Node])
        ==> res.left.asInstanceOf[Node].left.asInstanceOf[Node].isAVLTree)
    && ((res.left.isInstanceOf[Node] && res.left.asInstanceOf[Node].right.isInstanceOf[Node])
        ==> res.left.asInstanceOf[Node].right.asInstanceOf[Node].isAVLTree)
    // Knowledge probing about right heigh of rotated node
    && res.left.isInstanceOf[Node] ==> (res.left.asInstanceOf[Node].height == 1 + (res.left.asInstanceOf[Node].left.height < res.left.asInstanceOf[Node].right.height match {
      case true => res.left.asInstanceOf[Node].right.height
      case false => res.left.asInstanceOf[Node].left.height
    }))
    && res.right.isInstanceOf[Node] ==> (res.right.asInstanceOf[Node].height == 1 + (res.right.asInstanceOf[Node].left.height < res.right.asInstanceOf[Node].right.height match {
      case true => res.right.asInstanceOf[Node].right.height
      case false => res.right.asInstanceOf[Node].left.height
    }))
    //
    && res.left.isInstanceOf[Node] ==> (res.left.asInstanceOf[Node].height == 1 + (res.left.asInstanceOf[Node].left.height < res.left.asInstanceOf[Node].right.height match {
      case true => res.left.asInstanceOf[Node].right.height
      case false => res.left.asInstanceOf[Node].left.height
    }))
    // knowledge probing about keeping height
    && ((res.left.isInstanceOf[Node] && res.left.asInstanceOf[Node].left.isInstanceOf[Node])
      ==> (res.left.asInstanceOf[Node].left.asInstanceOf[Node].height == old(this).left.height))
    && ((res.left.isInstanceOf[Node] && res.left.asInstanceOf[Node].right.isInstanceOf[Node])
      ==> (res.left.asInstanceOf[Node].right.asInstanceOf[Node].height == old(this).right.asInstanceOf[Node].left.height))
    && res.left.isInstanceOf[Node] ==> (res.left.balanceFactor == (res.left.asInstanceOf[Node].left.height - res.left.asInstanceOf[Node].right.height))
    && res.left.isInstanceOf[Node] ==> ((res.left.asInstanceOf[Node].left.height - res.left.asInstanceOf[Node].right.height) <= 2)
//    && res.left.isInstanceOf[Node] ==> ((res.left.asInstanceOf[Node].left.height - res.left.asInstanceOf[Node].right.height) <= 2)
//    && res.left.balanceFactor <= 2
//    res.left.balanceFactor <= 1
//    res.left.isBalanced
  )
   //&& res.isAVLTree)
}
