import stainless.lang._
import stainless.collection._
import stainless.annotation._

sealed abstract class AVLTree {
  def test: Boolean = {
    this match {
      case Leaf() => true
      case Node(_,_,_,_) => false
    }
  }.ensuring(res => res == true)
}

case class Leaf() extends AVLTree
case class Node(v: Int, l: AVLTree, r: AVLTree, _height: Int) extends AVLTree {
  require(_height > 0)
}