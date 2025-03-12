#include <stdlib.h>
#include <stdbool.h>

/* Forward declaration of the BST node structure. */
typedef struct BSTNode BSTNode;

struct BSTNode {
    int value;
    BSTNode* left;
    BSTNode* right;
};

/*@
  // A logic predicate that defines membership in the BST.
  // This predicate mirrors the recursive structure of the tree.
  logic boolean bst_contains(struct BSTNode* t, int x) =
    (t == \null ? false : (x == t->value || (x < t->value ? bst_contains(t->left, x)
                                                           : bst_contains(t->right, x))));

  // A predicate stating that t is a binary search tree.
  predicate is_bst(struct BSTNode *t) =
    t == \null ||
    ( is_bst(t->left) &&
      is_bst(t->right) &&
      (\forall int x; bst_contains(t->left, x) ==> x < t->value) &&
      (\forall int x; bst_contains(t->right, x) ==> x > t->value) &&

    );
*/

/*@
  requires is_bst(t);
  assigns \nothing;
  ensures \result == bst_contains(t, key);
*/
bool contains(const BSTNode* t, int key) {
    if (t == NULL) return false;
    if (key == t->value) return true;
    else if (key < t->value) return contains(t->left, key);
    else return contains(t->right, key);
}
